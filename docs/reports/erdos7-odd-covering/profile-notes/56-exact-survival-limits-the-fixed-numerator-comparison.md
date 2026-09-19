[Index](../marked_head_profile.md) · [Actual source family](50-sharp-source-survival-endpoints.md) · [Actual source costs](51-sharp-off-diagonal-source-costs.md) · [Fixed numerator](49-full-linear-and-quadratic-carriers-refine-the-frontier.md)

# Exact survival limits the fixed-numerator comparison

Even exact source integration and exact mixed7 deletion payment cannot
bring the existing three-hinge survival comparison to403 while its
profile49 numerator is kept unchanged. Every finite upper target
certifiable in the comparison family specified below satisfies

    K_certificate >=
      86218021264866661646394378315020528544556307
      /208581453821091931839882213739521773400000
      =413.354206164557...>403.                         (ES1)

The witness is one actual finite-family limit. It constrains all three
survival hinges simultaneously, including h_(5/2), and pays the entire
actual mixed7 deletion. Thus this boundary permits improvements beyond
the source-only refinements of profile55.

This is a lower bound on the upper target obtainable from a specified
sufficient comparison. It is not a lower bound on actual K, an assertion
that the numerator bound is attained, or a resolution of unrestricted
Erdos #7. The proof is ordinary mathematics with exact arithmetic checks;
no Lean verification is claimed.

## 1. The actual family and its source law

Use the off-diagonal original forbidden family of profile50, truncated
at exponent height N>=3, and the original tensor35 test of profile51:

    Z=B3*B5,
    B3=1+sum_(a>=1)1_[7]_(3^a),
    B5=1+sum_(b>=1)1_[4]_(5^b).

Every original seven block uses this same test. In the seven coordinate
choose K_e=[4]_(7^e) for each positive exponent e. At finite height all
three sums end at N. CRT assigns one original residue per test modulus
3^a5^b7^e, so the complete test load is B3*B5*B7. Equal choices across
blocks specify this witness; no equality is imposed on arbitrary tests
in the comparison being bounded.

Let Lambda be the raw actual35 source measure, normalized only in the
seven coordinate by its pure7 surviving mass. Its limiting source mass
is s=1/4. The actual357 survivor masses satisfy S_N->D=3/20. The finite
shallow carrier mixture has

    pi_A=1-7^-N, pi_empty=7^-N, A=(0,1),

so only its limit is concentrated exactly on A. The source parameters
tend to the actual off-diagonal endpoint theta404.

The limiting raw pure3 measure eta gives B3=1 mass1/6, B3=2 mass2/9,
and B3=k mass2/3^k for k>=3. The actual35 ternary marginal lambda gives
B3=1 mass1/8, B3=2 mass5/72, and B3=k mass1/3^k for k>=3. Indeed the
deep nested test chain is in C4=[7]9, where lambda=(1/2)eta.

The cylinder[4]5 is source-free. Inside it, B5=m has raw five Haar
mass4/5^m for m>=2; outside it B5=1. Subtracting the[4]5 contribution
from the lambda marginal and adding its actual product law gives,
for every at-most-linear f,

    integral_Lambda f(Z)
      =(11/120)f(1)+(1/40)f(2)
        +sum_(k>=3)3/(5*3^k)*f(k)
        +sum_(m>=2)(4/5^m)*[
           f(m)/6+2*f(2m)/9+sum_(k>=3)(2/3^k)*f(k*m)].   (ES2)

These are the actual distribution masses. No source-envelope maximum
occurs in(ES2). They sum to1/4 and their first moment is17/24.

## 2. Every actual mixed7 deletion has seven test count one

All forbidden seven cylinders have the form

    G_(j,e)=[j*7^(e-1)]_(7^e).

The mixed classes are j=1,2,3,5 and the pure7 class is j=6. These
cylinders are pairwise disjoint as(j,e) varies. Each test K_e has
first digit4 and meets none of them. Therefore B7=1 on every mixed7
forbidden event, and the complete original test load there is Z.

The actual normalized pure7 test count has limiting probabilities

    p1=29/35, pn=36/(5*7^n) for n>=2, E B7=6/5.        (ES3)

For each forbidden class j the sum of all its normalized cylinder
masses is1/5. At height N it is instead

    kappa_N=(1-7^-N)/(5+7^-N).

Within one seven class the old35 forbidden carriers are disjoint, as
proved in profile50. Between different classes the old carriers may
overlap, but their seven events are disjoint. Their old-coordinate
indicator multiplicities must therefore be added, not replaced by the
indicator of their old-coordinate union.

For t>=1 put h_t(v)=(v-t)_+ and let H_t be its old35 integral against
this sum of mixed7 cofactor indicators. The actual removed hinge
integral is H_t/5 in the limit. Split the cofactors into b=0 and b>=1.

For b=0 all selected ternary carriers lie in root0, where B3=1. Their
total eta mass is1/6+1/9+1/18=1/3. The only five-coordinate strata with
nonzero h_t(B5) are source-free. This contribution is therefore

    (1/3)*sum_(m>=2)(4/5^m)*h_t(m).

For b>=1 the five residue is F_(4,b)=[4*5^(b-1)]_(5^b), source-free
across the pure3 survivor. The sum of ternary cofactor indicators is

    1+1_root1+1_C1+sum_(a>=3)1_[7+3^(a-1)]_(3^a).

Its weighted B3 distribution nu is

    nu(1)=5/18, nu(2)=4/9, nu(k)=5/3^k for k>=3,
    sum nu=1, sum k*nu(k)=77/36.                       (ES4)

For k>=3 the whole-space and root1 contributions give4/3^k. The
additional cofactor at ternary depth k contributes1/3^k. On F_(4,1)
the load B5 has masses4/5^m for m>=2. The other F_(4,b), b>=2, have
total mass1/20 and B5=1. Thus

    H_t=(1/3)*sum_(m>=2)(4/5^m)*h_t(m)
        +sum_(k>=1)nu(k)*[
           sum_(m>=2)(4/5^m)*h_t(k*m)+(1/20)*h_t(k)].   (ES5)

The omitted b=0, B5=1 term has zero hinge because t>=1. It is retained
in the complete finite histograms checked by the accompanying program.
All first moments are finite, and all series have complete affine
geometric tails.

## 3. Exact simultaneous survivor costs

Set C_t(v)=sum_n p_n*h_t(n*v) and U_t=integral_Lambda C_t(Z).
Equations(ES2)-(ES5) give the following exact raw integrals:

| t | U_t | H_t/5 |
| --- | --- | --- |
| 5/2 | 53959/147000 | 1831/18000 |
| 4 | 3321163/15435000 | 1777/33750 |
| 5 | 269853023/1620675000 | 75899/2025000 |

Every deleted load is Z. Consequently the actual raw surviving hinge
is U_t-H_t/5, and the three signed margins are

    d25=(7/2)*D-U_(5/2)+H_(5/2)/5=45803/176400,
    d4=D-U4+H4/5=-115939/9261000,
    d5=D-U5+H5/5=5098909/243101250.                     (ES6)

These exact deletion integrals already pay all shallow and deep
deleted events. Adding the earlier conditional27/81 credits again
would double-count part of that payment.

These values are approached by the same genuine finite original
families. To justify the limit, the untruncated tensor B3*B5*B7 has
finite Haar mean(3/2)(5/4)(7/6)=35/16. All normalized finite pure7
densities are bounded by6/5. The source indicators converge pointwise,
and the old-coordinate sum of class indicators is bounded by4 because
each of the four classes has disjoint carriers. Thus the finite source
and deletion hinge integrals are dominated by fixed integrable
functions. Dominated convergence supplies(ES2)-(ES6) as actual limits;
finite exponent sampling is not the proof of these quantifiers.

## 4. The fixed-numerator comparison family

Keep the physical AP11/T4, AP13/T5 survival functional

    rho_actual*S >= (919/924)*S
                    -(1/22)*V25-(1/6)*V4-(4/33)*V5,     (ES7)

where Vt is a raw upper bound valid for every corresponding original
test on the same actual source law. The tests retain independent
residue choices. This survival inequality does not hold with arbitrary
chosen test costs substituted for their uniform upper bounds.

Equivalently, with barriers C25=7/2, C4=C5=1 and q=23/42, any uniform
combined lower margin must satisfy

    M(theta,pi) <= (C25*S-W25)/22
                  +(C4*S-W4)/6+(4/33)*(C5*S-W5),         (ES8)

where Wt are the raw actual surviving costs of any admissible triple
of original tests. Taking all three to be the tensor witness above
is allowed. This is the uniform comparison obligation that(ES7)
consumes, not an assertion about rho for one selected test triple.

For separate margins its value is

    M(theta,pi)=sum_c pi_c*[m25(theta;c)/22
                            +m4(theta;c)/6+(4/33)*m5(theta;c)].

A combined margin may also be used directly, provided(ES8) holds for
every finite actual source and every admissible original test triple.
This allows exact source bounds, exact mixed7 deletion and improvements
to all three margins.

For the endpoint comparison assume(ES8) also applies at the actual
limit, or explicitly assume the whole mixture margin admits that limit:

    M(theta404,delta_A)
      <=liminf_N M(theta_N,pi_N).                        (ES9)

Lower semicontinuity of M as a function of(theta,pi) is sufficient.
In particular it follows from continuity of all finitely many carrier
margins near theta404. The condition is on the whole mixture. Lower
semicontinuity of the A component alone does not exclude a negatively
divergent empty component weighted by pi_empty.

Apply(ES8) to the actual finite family and then use(ES9) and(ES6).
This bounds the endpoint combined margin and hence its denominator:

    M(theta404,delta_A)<=d25/22+d4/6+4*d5/33,
    q*D+M(theta404,delta_A)<=Dmax,
    Dmax=q*D+d25/22+d4/6+4*d5/33
        =12117093811/128357460000>0.                     (ES10)

No separate attainment assumption is needed: the same actual test
provides all three costs. Signed margins, including d4<0, cannot be
clipped to zero.

Retain profile49's numerator comparison at the same control and
carrier. Its exact limiting numerator and offset are

    Nfixed=16632177193488738812476720877032433019439
            /449729701159543356783713630148000000000,
    C0=185694867601/8599322160.                          (ES11)

The original fixed-target comparison must imply

    (K-C0)*(q*D+M(theta404,delta_A))>=Nfixed.              (ES12)

If the mass coefficient selects the s endpoint instead, its inequality
is stronger than(ES12), so(ES12) remains necessary. Since Nfixed>0,
a nonpositive denominator cannot yield a valid finite upper target
with K>=C0. With a positive denominator, (ES10)-(ES12) imply

    K>=C0+Nfixed/Dmax,

which is exactly(ES1). The numerator is the unchanged comparison
expression; it need not be attained by the tensor witness that bounds
the denominator. This distinction is essential to the scope of(ES1).

Changing the numerator comparison, the survival functional or its
weights, or retaining a genuine numerator-denominator joint constraint
is outside this comparison family. Within it, better observations of
the same three survival costs cannot suffice to reach403.

## 5. Exact reconstruction

The [checker](../frontier/exact_survival_comparison_boundary.py) and
[result](../certificates/source_norms/exact_survival_comparison_boundary.json)
use only canonical source and certificate inputs. They pin the actual
source constructor, profile49 and profile53, the inherited source
profiles and carrier table, and the corresponding implementations.

At heights3,4,5,6 the checker builds the actual forbidden masks from
their original residues. Every mass in each complete source-load
histogram and each multiplicity-weighted removed-load histogram agrees
with an independently derived finite distribution law. The eight
histograms retain their load-one terms. They produce twelve finite
three-hinge costs, while the original seven cylinders independently
verify B7=1 on every removed event.

For the limiting formulas, the program integrates the complete actual
35 distribution before the seven expectation, and independently
combines the seven expectation first. Both orders agree exactly. The
removed costs are also evaluated in both orders of the ternary and
five sums. Geometric tails are summed algebraically, never replaced
by a finite cutoff.

The fixed square margin5701/3888 is recovered from the pinned49
aggregate and the pinned complete quadratic-tail weight. The remaining
numerator terms are reconstructed at404/A; the same recovered numerator
reproduces profile49's K exactly before replacing the denominator.
No source39 vertex scan or temporary artifact is required.

Default execution reconstructs without writing. To compare the current
canonical result as well, run

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/exact_survival_comparison_boundary.py --check
```

Only an explicit `--output PATH` writes a result. All checks use active
exceptions, including under `-O`. The ordinary proof supplies the
universal comparison and limiting arguments; these arithmetic checks
validate its concrete input distributions and constants.

## 6. Restoring exact AP11 dilation still leaves a boundary above412

The survival functional has constrained freedom. Profile35 derives
the three-hinge coefficients from physical AP11/T4 and AP13/T5.
Changing those physical thresholds changes their caps and the
numerator comparison too; those changes are outside(ES1). With the
same physical caps, one can improve the survival expression by
restoring the complete AP11 auxiliary count before its final
three-hinge compression.

For AP11/T4 the comparison count L has the exact law

    p11(1)=28/33,
    p11(n)=50/(3*11^n) for n>=2,
    E L=7/6.                                           (ES13)

These are auxiliary comparison counts, not a claim that the actual
bad events are independent. The general same-law bound from profile35
is

    rho>=1-H(4)/6-E[L*H(5/L)]/7,                       (ES14)

where every H(t) is a uniform bound for all original old-test hinges
on the same actual357 law. Its three-hinge reduction uses, for n>=2,

    h5(n*v)<=n*h_(5/2)(v)+(n-2)*(5/2).                  (ES15)

The proof of(ES15) is exact for v>=5/2. Restoring(ES14) means keeping
its complete dilation costs, while preserving the independent
original blocks and their allowed residues. To bound this enlarged
comparison family from below, choose every block to be the same
actual tensor witness. It simultaneously supplies all the dilated
costs; no common maximizer is inferred for arbitrary tests.

On this witness the complete load A=B3*B5*B7 is an integer. The only
possible losses in(ES15) therefore occur at A=1 and A=2. Let mu_j be
their raw actual surviving masses. Equations(ES2)-(ES5) give

    mu_1=(29/35)*(11/120)-(1/5)*(71/360)=23/630,
    mu_2=(29/35)*(31/600)+(36/245)*(11/120)
             -(1/5)*(3/25)=949/29400.                  (ES16)

For example, the old source masses of Z=1 and Z=2 are11/120 and
31/600. The corresponding cofactor-weighted masses are71/360 and
3/25. The second pre-deletion mass additionally includes B7=2,Z=1.
Mixed7 deletion always has B7=1, as before.

Define the complete expected compression loss at load v by

    Delta(v)=sum_(n>=2)p11(n)*[
                 n*h_(5/2)(v)+(n-2)*(5/2)-h5(n*v)].

It vanishes at every integer v>=3. For v=1, the n=3,4,5 losses are
5/2,5,15/2, while the loss is3n/2 for every n>=6. For v=2 the loss
is n/2 for every n>=3; n=2 has zero loss in both cases. Summing
these complete geometric tails yields

    Delta(1)=6653/175692,
    Delta(2)=31/1452.                                  (ES17)

Consequently the exact improvement in this actual witness's raw
survival functional is only

    gain=[mu_1*Delta(1)+mu_2*Delta(2)]/7
        =32101757/108472240800
        =0.00029594444406462375... .                    (ES18)

Even uniform exact bounds for every cost in(ES14) cannot give a
larger denominator at this witness than

    Dmax_exact=Dmax+gain
              =4044603032429/42710944815000.

The same endpoint/whole-mixture condition used in section4 applies
to the new comparison. Keeping Nfixed and C0 unchanged therefore
still forces

    K_certificate>=C0+Nfixed/Dmax_exact
      =5072478916121259734553727325478823117587871
        /12307961740440067066961922810098815200000
      =412.12988983014947...>403.                       (ES19)

This removes exactly one relaxation, namely(ES15). It does not
optimize the physical kernels or exploit overlap between their
actual bad events. Nor is(ES19) a lower bound on actual K.

The necessary raw denominator gain to reach403 with the fixed
numerator, even before paying a positive core error, is

    Nfixed/(403-C0)-Dmax=0.002562753228675973...,

which exceeds(ES18). Thus restoring the exact dilation alone does
not evade the actual witness. A further survival improvement must
prove a new uniform inequality, for example using actual bad-event
overlap or occupied-root geometry, and supply enough gain on this
witness. Alternatively the numerator or a joint numerator-denominator
comparison must change. Passing this one witness remains a necessary
condition, not a uniform proof.

The checker includes(ES16)-(ES19). As an independent integration
check it reconstructs the raw actual first moment41/72 and the
load atoms1,...,4. For n>=5,

    integral h5(n*A)=n*(41/72)-5*D,

and for n<5 it adds the exact corrections at n*A<5. The resulting
complete AP11 expectation reproduces Dmax_exact independently of
the two-loss calculation in(ES17)-(ES18).
