# Retained-leaf lower bounds admit29 at both opposing depth-two profiles

The two star profiles that limit the unmodified fixed-weight source bound in
[Report792](792-optimal-fixed-leaf-weights-admit-the-complete1200-tail.md)
both admit arbitrary29-ending originals once nonnegative leaf survival is
retained in the mass estimate. The same original full probability law is
used for every subsequent query and moment. After all remaining support
primes strictly above3000, the distorted survivor masses exceed3/20 and7/100,
respectively.

The head is literally P8=(3,5,7,11,13,17,19,23). Originals supported wholly
on this head have v3<=2 and satisfy one of the two stated star contracts.
Other old exponents, mixed old supports and their phases are arbitrary.
Originals involving29 or a prime above3000 have arbitrary globally fixed
phases and arbitrary finite exponents. No support prime31 through3000 is
included. The conclusion is not uniform over star profiles and does not
resolve unrestricted Erdős #7. These are ordinary mathematical arguments
and exact arithmetic, not Lean verification.

## 1. The original law and the two actual star contracts

Retain the actual five nine-leaves from
[Report790](790-shared-pair-deficits-admit-twenty-nine-at-a-depth-two-profile.md),
with root groups A={0,1}, B={2,3,4}. Leaf names refer to one permitted
choice after avoiding the actual pure3 and9 originals, using additional
source-only exclusions if necessary. For example the remaining numerical
leaves can be(4,7,2,5,8) modulo9. Original phases are never renamed
independently or chosen anew at a later stage.

Use the full original probability weights from792:

    w=(a,a,b,b,b),
    a=525243426/2350861343,
    b=1300374491/7052584029,       2a+3b=1.              (RL1)

For q in Q=(5,7,11,13,17,19,23), a role(r_q,t_q) requires every old3q^j
original meeting these leaves to have ternary root r_q, and every old9q^j
original meeting them to have ternary leaf t_q. Here root0 means A and
root1 means B. Originals missing the retained leaves impose no role
condition. No q-adic phase or nonternary height restriction is imposed.
The two contracts, in increasing q order, are

    Lplus =((1,2),(0,0),(0,1),(0,1),(0,1),(0,1),(0,1));
    Lminus=((0,0),(1,2),(1,3),(1,4),(1,3),(1,4),(1,4)). (RL2)

Let lambda_q be normalized Haar on the actual pure q-power survivor and
C_q=(q-1)/(q-2). As in790,

    lambda_q(a mod q^e)<=C_q/q^e,
    b_q=1/(q-2),
    m_(q,l)=1-b_q[1_(group(l)=r_q)+1_(l=t_q)]>0.      (RL3)

Downscale each actual star restriction to exactly m_(q,l), as in789--791.
This supplies one supported submeasure on each leaf. Let U avoid every
actual old original. The original full product source remains

    lambda_w=lambda3,w tensor product_q lambda_q,
    alpha=lambda_w(U),
    mu=lambda_w|U/alpha.                              (RL4)

The ternary suffix above depth2 remains Haar. Subsequent query comparisons
use this full lambda_w and its restriction mu.

## 2. Nonnegative leaf survival improves the mass lower bound

For the common actual mixed-support allocations c_D, let S_l>=0 be the
true surviving mass of the exactly downscaled star source on leaf l, and
let R_l(c) be its signed support-polynomial response. Report790's one-clique
argument gives S_l>=R_l(c), including when R_l(c)<0. Therefore, for any
fixed coefficients0<=h_l<=w_l,

    alpha>=sum_l w_l S_l>=sum_l h_l S_l>=sum_l h_l R_l(c). (RL5)

The discarded leaves are used only through S_l>=0. They are not removed
from the original query source inRL4, and h is not renormalized into a new
probability law.

Apply the shared-deficit bound of791 to the last expression with coefficients
h instead of w. All terms remain affine in each actual completed mixed
allocation, and endpoint deficits stay nonnegative. With h-weighted first
terms A_D, pair terms P_DE, triples T_DEF and root mass S0, its cancelled
form is

    F_L(h)=S0-sum_(D:degD=0) max A_D
              +sum_(D,E disjoint) min[P_DE-A_D/degD-A_E/degE]
              -sum_(D,E,F disjoint) max T_DEF.          (RL6)

There are120 mixed supports,546 disjoint pairs and210 disjoint triples.
The nonzero endpoint degrees are26,11,4,1; all eight zero-degree deficits
are discarded. Each positive-degree deficit is divided once among its
incident edges. The same original c_D occurs in every term; pairwise
minimizers need not be jointly realizable to furnish lower bounds on that
one common evaluation. EquationsRL5--RL6 prove

    alpha>=F_L(h).                                    (RL7)

For Lplus take h=(a,a,0,b,b), and for Lminus take h=(0,a,b,b,b). Exact
baseline-plus-credit evaluation gives

| Contract | Separate-extrema baseline | Shared pair credit | Full-source mass lower alpha_* |
|---|---:|---:|---:|
|Lplus|598359365099824/18694460800271025|4659455708887193/594068420986390350|213065879798534401/5346615788877513150|
|Lminus|168218552316986/11216676480162615|3843060730611248/243027990403523325|1321375770143402/42887292424151175|

The alpha_* values are0.03985060610522496... and0.03081042647959968.... All
546 edge credits are positive in each evaluation. Both bounds concern
alpha of the FULL original lambda_w, not the normalized retained-leaf
submeasure.

This changes the mass certificate used in792--793. It does not contradict
an optimality statement about their unmodified signed response. Selecting
masks separately at vertices does not establish a valid vertex reduction
for a clipped objective. No such reduction or uniform star theorem is
claimed here;RL2 fixes exactly the two contracts being evaluated.

## 3. The complete query comparator keeps the original full weights

Use790's conditional weighted-hinge rearrangement on lambda_w. It permits
independent phases at different numerical query labels; no physical
matching-prefix-run factorization is assumed. Its auxiliary independent
runs have tails

    Pr(J3>=1)=r=max(2a,3b)=1300374491/2350861343;
    Pr(J3>=e)=v*3^(2-e), e>=2,
      v=max(a,b)=525243426/2350861343;
    Pr(Jq>=e)=C_q/q^e, e>=1.                         (RL8)

These are the ORIGINAL full-law caps. Neither r nor v is recomputed from
h. Put M=product_(p in P8)(1+J_p). Its full mean is

    EM=(1+r+3v/2)product_q C_q=18182557585408/4196287497255.

For t>=1, define H(t)=E(M-t)_+. The same-source comparison gives

    B(mu)<=t+H(t)/alpha_*.                           (RL9)

Here B includes the numerical unit. At an integer threshold the exact
complete hinge is

    H(t)=EM-t+sum_(j<t)(t-j)Pr(M=j).                  (RL10)

Only the subthreshold atoms are enumerated. The full mean inRL10 retains
every larger load and all original exponent tails.

For Lplus the minimizing threshold is14; for Lminus it is16. The exact
consumer verifies in each case

    Pr(M>t)<=alpha_*<=Pr(M>=t).                      (RL11)

The left and right derivatives of t+H(t)/alpha_* have opposite signs under
RL11, so these thresholds minimize the complete real-threshold comparator.
This is a global convexity certificate, not a sample of thresholds.
The resulting bounds are

    Bplus <=23.458013112172505...<28;
    Bminus<=25.68567787055517...<28.                   (RL12)

Exact rational hinges and bounds are retained in the result data.

## 4. One source continues through29 and the complete3000 tail

Take the actual pure29 survivor law with cylinder cap(28/27)29^-e.
The complete remaining29-ending inventory has nonunit old cofactors, so
790's same-source union bound gives mass at least

    m29=(28-B_*)/27.                                 (RL13)

All old cofactor query heights are permitted here; they are not inserted
as extra old forbidden originals. Use the unchanged full-law raw fourth
query envelope from792,

    K0=(1+15r+216v)product_q[1+C_q A4(q)]
      =1995816314082394584902043010164181 /
        6513156637804234575590400000,
    A4(q)=15s+50s^2+60s^3+24s^4, s=1/(q-1).

The same unnormalized post29 survivor has mixed fourth envelope

    K29=(K0/alpha_*)[1+(28/27)A4(29)],
    1+(28/27)A4(29)=120361/74088.                     (RL14)

Use [Report734](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md)
with delta=2/7, growth exponent21, cutoff3000 and ell=7, exactly as790.
Its complete prime-tail factor is

    tau=(21609/10240)(99/97)^21 [3000/2999^4]
           sum_(j=0..21)21!/[(21-j)!21^j].            (RL15)

Its coefficient and analytic range premises are inherited at their stated
scope; the exact consumer checks the applicable coefficient inequalities.
All future originals keep their complete numerical labels and fixed phases.
Their finite number and exponents have no additional bound.

| Contract | m29 lower bound | m29-K29*tau | Simple final lower bound |
|---|---:|---:|---:|
|Lplus|0.16822173658620357...|0.1585695134844238...|>3/20|
|Lminus|0.08571563442388248...|0.07323132359736854...|>7/100|

These are distorted supported masses, not final Haar-density bounds. Every
quantity in a row belongs to the same original lambda_w restriction and
its actual subsequent continuations. Positive mass gives an actual finite
CRT survivor.

## 5. Exact verification and additional scope

The [consumer](../../../frontier/cover-geometry/refined-capped-source/depth_two_leaf_retention.py)
rebuilds all support sets and all100 role choices on every disjoint pair.
It computes the baseline and nonnegative shared credits independently of
the cancelled expressionRL6, then reconstructs the original full comparison
law, exact subthreshold atoms, quantile conditions, pure29 allowance and
complete prime tail. It reuses the existing adjacent quartic/tail arithmetic.
The [result](../../../frontier/cover-geometry/refined-capped-source/depth_two_leaf_retention.json)
is compared with a fresh exact replay under ordinary and optimized Python.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/depth_two_leaf_retention.py
```

The two star contracts differ from790's contract even after the permitted
within-root leaf permutations: its root1 assignments occur at5 and23,
whereasRL2 assigns root1 only at5, or at every q except5. Families with29
present also have nine support primes below1200, so792's at-most-eight-small-
primes theorem does not cover these general phase classes. The new assertion
is the continuation for these two fixed contracts with arbitrary remaining
old mixed classes and arbitrary29 classes. It is not an assertion that every
member was outside every earlier restricted result.

Arbitrary star allocations, arbitrary wholly-old ternary heights, and
additional support primes31 through3000 remain outside this theorem.
Leaf nonnegativity is a valid mass resource; a uniform way to use it while
retaining the actual common-source query boundary remains unresolved.
