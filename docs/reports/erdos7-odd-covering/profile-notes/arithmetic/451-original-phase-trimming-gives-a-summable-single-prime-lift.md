[Index](../../marked_head_profile.md) · [Uniform-lift boundary](450-weighted-original-depths-and-the-uniform-lift-boundary.md) · [Actual lifting](439-actual-residual-lifting-and-exact-free-coordinate-cost.md) · [Full-history kernels](../../problem-details/04c-full-history-capped-laws-and-exact-global-optimization.md)

# Original-phase trimming gives a summable lift for single outside primes

The harmonic completion load of report450's uniform lift is avoidable in a restricted original-label family. If each tail label is of the form3^e a p^f with a dividing a fixed head Q and just one outside prime p, one can remove its early ternary-depth cylinders before choosing the outside coordinate. A single supported law then preserves an arbitrary given core marginal and has a geometrically decaying completion bound as p increases. All finite outside prime-power heights are allowed.

For Q=1225, the combined completion contribution of any finite set of outside primes p>=43 is less than1/4, uniformly in every original ternary height, outside prime-power height and residue choice. This is a marginal-preserving lifting estimate for the specified label class. It supplies neither the core margin nor an estimate for cofactors involving multiple outside primes, and does not settle unrestricted Erdős #7.

These are ordinary mathematical deductions with exact finite controls, not new Lean certification or a mathematical-priority claim. Normalized conditional kernels and finite union bounds are reused; the content here is their explicit application to the original weighted completion inventory, including a uniform tail sum.

## 1. Actual core, original labels and one supported law

Let K be odd and coprime to3, let Q divide K, and put D=tau(Q), the number of positive divisors of Q. Let P be any finite set of primes coprime to3K. Resolve the ternary exponent of the entire original family by a common finite H>=1, and each outside exponent by a finite J_p>=1. Its distinct numerical moduli greater than one consist of:

* arbitrary core labels dividing3^H K;
* tail labels3^e a p^f, with p in P, a dividing Q,0<=e<=H and1<=f<=J_p.

Each numerical label has at most one original residue. Labels may be missing and all supplied residues are arbitrary. Labels involving two members of P are excluded. No assumption of comparable-class disjointness or coherent residues is needed.

Let S be the set in Z/K avoiding all original3-free core classes. Assume S is nonempty and let mu be ANY probability supported on S. It is chosen once. The output law will preserve this whole K-marginal, not merely its Q-projection or a scalar head bound.

For a tail label d=3^e a p^f write its actual cofactor cylinder as

    C_d = {(x,y): x=a_d mod a, y_p=a_d mod p^f}.

The original residue a_d is retained also at its ternary coordinate. The completion task being bounded here uses C_d and the weight3^(1-e) for e>=1; removing the ternary coordinate in this named task does not replace the full original class by a new modulus.

Let H_p denote normalized Haar measure on Z/p^J_p, and put

    R_p=sum_(f=1,...,J_p)p^(-f)
       =(1-p^(-J_p))/(p-1).

For each p choose an integer0<=E_p<=H such that

    eta_p=1-D(E_p+1)R_p > 0.                                (PT1)

At a fixed actual core point x in S, let F_p(x) be the UNION of the literal p-adic cylinders from all original labels3^e a p^f with0<=e<=E_p whose a-coordinate matches x. For each pair(e,f) there are at most D original labels, and each p-cylinder has H_p-mass p^(-f). The union bound gives

    H_p(F_p(x)) <= D(E_p+1)R_p,
    H_p(F_p(x)^c) >= eta_p.

Overlapping cylinders are counted only in this upper estimate; the kernel uses their actual union. Define k_p(x,.)=H_p(. | F_p(x)^c), and define one law by

    nu(x,(y_p)_p) = mu(x) product_p k_p(x,y_p).               (PT2)

Every row is normalized. Therefore nu preserves mu exactly. It avoids every3-free tail class, since those phases were included at e=0, and avoids all3-free core classes because x belongs to S. Thus nu is supported on the actual3-free residual R_3 of the full family.

Conditional independence of the outside coordinates holds given x. Unconditional independence need not hold: different actual core points can exclude different p-phases. All these kernels are fixed by the original input before evaluating any cylinder. They do not reselect an original residue or supply a new probability law for each test.

## 2. The simultaneous finite-height completion estimate

Under the SAME law(PT2), every original tail cylinder has the conditional bounds

    nu(C_d | x)=0,                                    e<=E_p;
    nu(C_d | x)<=p^(-f)/eta_p,                        e>E_p,

where a nonmatching a-coordinate gives zero in either line. For e>=1 define

    L_p(nu) = sum_(original d=3^e a p^f, e>=1) 3^(1-e) nu(C_d).

There are at most D original labels at each(e,f), so if E_p<H,

    L_p(nu)
      <= [3D R_p/(2 eta_p)] 3^(-E_p)
                            [1-3^(-(H-E_p))].                (PT3)

Indeed, the remaining geometric sum is

    sum_(e=E_p+1,...,H)3^(1-e)
       = (3/2)3^(-E_p)[1-3^(-(H-E_p))].

If E_p=H, the contribution is exactly zero. In particular p-1>D(H+1) permits deleting every supplied tail cylinder in that p-coordinate at every finite outside height while preserving the given core marginal. The finite-height condition(PT1) can be weaker.

When J_p=1, R_p=1/p and R_p/eta_p=1/[p-D(E_p+1)], recovering the literal residue-count bound. At arbitrary finite J_p, whenever p-1>D(E_p+1),

    R_p/eta_p <= 1/[p-1-D(E_p+1)],

because t/(1-D(E_p+1)t) is increasing before its pole and R_p<=1/(p-1). Thus one bound controls every outside exponent height without replacing any original p^f label by p.

The bound uses the inventory size D even when many labels are missing or their head projections do not match x. Retaining those actual counts can improve it. There is no claim that the displayed envelope is sharp for arbitrary original families.

All p estimates coexist under(PT2), hence may be added. This addition is an upper bound on the linear completion sum of original labels. It is not addition of overlapping deletion credits such as the invalid operation in450.

## 3. A uniform quarter-budget for Q=1225 and p>=43

Here D=9. For an upper envelope uniform in BOTH ternary and outside heights set

    c_p(E)=27/[2*3^E*(p-1-9(E+1))],

whenever E>=0 and p-1>9(E+1). For p>=15 its minimum is attained at

    E_*(p)=floor((p-15)/9),
    r_*(p)=p-1-9(E_*(p)+1) in {5,...,13}.                     (PT4)

To check the minimum, write r=p-1-9(E+1). When the next E is admissible, the ratio c_p(E+1)/c_p(E) is r/[3(r-9)]. It is less than one exactly when r>27/2. The integer remainder at the minimum therefore lies between5 and13. For finite H use E_p=min(H,E_*(p)); if the minimum is H, (PT3) is zero, and otherwise it is bounded by c_p(E_*(p)).

This gives one family-independent summable majorant. It is enough to sum over every odd integer n>=43 and remove five known composites; no asymptotic prime theorem or prime cutoff computation is required. The nine envelope values at43,45,...,59 are

    1/12,1/16,1/20,1/24,1/30,1/42,1/54,1/66,1/78.

Advancing n by18 advances E_* by2 and preserves r_*, so c_(n+18)=c_n/9. Therefore

    sum_(odd n>=43) c_n(E_*(n))
      =(9/8)(1/12+1/16+1/20+1/24+1/30
                             +1/42+1/54+1/66+1/78)
      =147517/384384.

Remove the terms at the composites45,49,51,55,57. Thus for every finite P of primes at least43,

    sum_(p in P) L_p(nu)
      <= 147517/384384-1/16-1/24-1/30-1/54-1/66
       = 3677489/17297280
       = 1/4-646831/17297280 < 1/4.                         (PT5)

If every J_p=1, the stronger first-power envelope instead gives282301/1153152<1/4 by summing its odd-integer tail43413/128128 and removing the45 and49 terms1/18 and1/26. These two rational upper bounds use different composite subtractions and are not asserted to be sharp or ordered by model generality. The quarter-budget applies only to primes at least43; it is not a bound for all primes greater than7.

## 4. What the lifting bound supplies to the original covering problem

Every core cofactor event depends only on x, so(PT2) leaves its completion mass unchanged. Write L_core(mu) for the original3-bearing core completion sum, excluding pure powers of3, with the same weights3^(1-e). Then

    L_comp(nu)=L_core(mu)+sum_p L_p(nu).                      (PT6)

For completeness, whole coverage forces

    L_comp(nu) >= B_H=(3+3^(1-H))/2                           (PT7)

for EVERY law on R_3. At each3-free residual point, the original pure3 classes occupy at most sum_(e=1,...,H)3^(-e) of the ternary coordinate. All remaining covering classes contribute at most sum_d3^(-e_d)1_Cd at that point. A ternary union bound, multiplied by3 and then integrated against the single law, proves(PT7), as in378.

Consequently, for the stated single-outside-prime family with p>=43, any actual core law satisfying

    L_core(mu) <= B_H-1/4                                   (PT8)

proves noncoverage after adding arbitrarily many of these tail primes: (PT5)--(PT6) give L_comp(nu)<B_H. The existence of a law satisfying(PT8) is an additional obligation, not a consequence of a small head Gamma or of the trimming construction.

In450's702-label family the original3-free outside phase is0 and every mixed outside phase is1. Deleting these two values at each p leaves the nonempty set{2,...,p-1}; the same construction then gives every mixed completion event mass zero, regardless of its ternary depth. This is a special simplification using its ACTUAL repeated phases. It does not assert zero load for arbitrary independent phases.

The support assumption matters. With original classes0 mod43, 0 mod47 and1 mod2021, independent kernels excluding only the two pure-prime zero phases still assign positive mass to the forbidden joint class1 mod2021. That original label uses two outside primes and is not of the admitted shape; actual residual support then requires a joint constraint. Larger head divisor inventories change D and its numerical tail budget. No complete-layout Gamma bound is asserted for(PT2).

## 5. Reuse and verification boundary

Reports439--440 retain the actual-fibre and shared-law lifting obligations. Chapter04c already constructs normalized full-history kernels preserving previous marginals, and Chapter32 gives a different conditional comparison and prime-tail bound. Chapter06's shallow/deep split concerns blocked fibres of original two-prime edges; the present tail labels can contain3,5,7 and p simultaneously. These results do not by themselves provide the explicit original-depth cylinder budget D(E+1)R_p, the envelope(PT3), or the arbitrary-core-marginal quarter-budget for this inventory. The present elementary construction does not claim a new general kernel theorem or a new unrestricted prime-support exclusion.

The [exact control program](../../frontier/cover-geometry/original_phase_trimmed_lift.py) and [data](../../frontier/cover-geometry/original_phase_trimmed_lift.controls.json) check literal original residues, normalized kernels, actual3-free support, common-law cylinder masses, finite-height bounds and the rational tail sum. The proof above covers all finite heights, all admitted original residue choices and arbitrary finite tail prime sets; finite controls alone do not establish those quantifiers.

The first-power control has121 original classes and one30,260-atom law with two outside coordinates and a22-atom actual head marginal. It checks108 original cofactor events and164247 occupied phase cells under that one law. Its two positive late loads are65/22599 and73/28350, below their respective finite-height bounds4/63 and4/99. A separate p^2 control has38 original classes and one150-atom law: at one head point the early cylinders have nominal cardinality96 but union cardinality68, so the actual kernel retains53 of121 leaves. Its positive late load is100/15423<=64/75, with1650 literal3-free membership checks. The controls also verify zero completion load for450's552 original mixed events, rejection of reusing one head point's kernel at another, and the positive forbidden mass1/1932 in the43/47/2021 support counterexample.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/original_phase_trimmed_lift.py
```

The unresolved bridge is a comparable construction with labels coupling multiple outside primes and a sufficient actual core margin, while retaining one law for the complete original family.
