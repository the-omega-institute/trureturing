# Retaining the core intersection reduces finite phase contracts

Keeping the intersection of every remaining original cylinder with the reference core gives a sufficient contract on only23 shallow numerical labels. With the fixed five-leaf weights(3/16,3/16,5/24,5/24,5/24), the same actual source admits arbitrary29 originals and every finite prime tail strictly above3000, with final distorted mass greater than3/50.

The generic union charge in [Report800](800-finite-shallow-phase-contracts-admit-arbitrary-ternary-heights.md) pays for an entire cylinder even where the reference core already excludes it. At that report's original weights, intersection accounting alone reduces103 sufficient labels to52. Choosing one different fixed law gives the23-label result here; no query or deletion term selects its own law.

The intersection estimate extends to any one fixed symmetric five-leaf law. Its lower bound is separately concave in the seven actual reference-hit probabilities, so all128 box vertices suffice. The actual probabilities occur jointly in the core mass and all deletion terms. No simultaneous attainment of the individual cylinder caps is assumed.

This is an ordinary conditional argument with exact rational verification, not new Lean verification or a solution of unrestricted Erdős#7. All original moduli remain odd, nonunit and pairwise numerically distinct. The support is contained in{3,5,7,11,13,17,19,23,29} and a finite set of primes strictly above3000. In particular primes31 through3000 remain excluded. The finite shallow phase-null contract below remains a substantive hypothesis; every unlisted phase and every higher ternary height is arbitrary.

## 1. One actual source and one reference core

Use Report800's common full CRT carrier and common normalization of the pure3/9 originals. Their absent and redundant cases are handled by auxiliary source restrictions, as in [Report719](../700-749/719-actual-phase-unions-and-common-affine-reference-enlarge-the-certified-families.md). Every actual mixed phase is transported by the same map. No reference class is asserted to be an additional actual original.

Let Q=(5,7,11,13,17,19,23). On each q-coordinate take the actual normalized survivor law lambda_q of all pure-q-power originals. Numerical distinctness gives

    lambda_q(c modq^j)<=C_q/q^j,
    C_q=(q-1)/(q-2),    beta_q=C_q/(q-1)=1/(q-2).

For fixed positive rational a,b with2a+3b=1, put weights(a,a,b,b,b) on the ternary leaves(4,7,2,5,8), with Haar suffixes above depth2. Set

    lambda=lambda_3 tensor product_(q inQ)lambda_q.

The source is chosen once, before every query or deletion. Define E_q={x_q=2 modq} and the ACTUAL probabilities t_q=lambda_q(E_q). They satisfy0<=t_q<=u_q=C_q/q. The reference core G excludes all pair events E_p intersect E_q. On ternary root1 it also excludes E_5; on root2 it excludes all E_q withq!=5. Thus, on root1 the core means no5 hit and at most one non5 hit; on root2 it means no non5 hit and places no constraint on the5 hit.

For D subset Q, force the hit indicators in D to zero and define

    B_D(t)=product_(q notinD,q!=5)(1-t_q),
    A_D(t)=(1-1_(5 notinD)t5)
      *[B_D(t)+sum_(q notinD,q!=5)t_q
          product_(r notinD,r!=5,q)(1-t_r)].

These are probabilities of the two root events with queried coordinates removed. In particular the exact reference core mass is

    M(t)=2a A_empty(t)+3b B_empty(t).                    (RC1)

Both responses are separately affine in every t_q. The actual source need not attain any endpoint of their cap box.

## 2. A remaining original is charged only inside the core

Let n>1 be Q-smooth, D=supp(n), and c_n=C_D/n where C_D=product_(q inD)C_q. Fix any one actual n-cylinder, with arbitrary phases. It determines each first-digit hit in D. The core event is decreasing in all hits, so replacing those determined bits by zero can only enlarge it. Independence of the coordinates under the original product source therefore gives

    lambda(nonternary cylinder intersect root-core)
      <=c_n A_D(t) or c_n B_D(t).                       (RC2)

The phase pattern need not maximize the pure-cylinder probability and the core probability simultaneously. Equation(RC2) is an upper bound for their one actual product, obtained by monotonicity and the uniform cylinder cap.

For an original modulus3^h n, the full core-intersection upper caps are

    h=0: c_n F_(D,0),    F_(D,0)=2a A_D+3b B_D;
    h=1: c_n F_(D,1),    F_(D,1)=max(2a A_D,3b B_D);
    h=2: c_n F_(D,2),    F_(D,2)=max(a A_D,b B_D);
    h>=3: c_n 3^(2-h) F_(D,2).                         (RC3)

For h=1, a phase selects one root; for h>=2 it selects one leaf and then its Haar suffix. A forbidden pure3 or9 cylinder has zero mass and was removed before this calculation. Pure-q cylinders are already null under lambda_q, so h=0 is charged only when|D|>=2.

Every support has the exact complete cofactor budget

    beta_D=sum_(supp(n)=D)c_n=product_(q inD)1/(q-2),
    beta_empty=1.                                      (RC4)

The sum of3^(2-h) overh>=3 is1/2. Consequently EVERY high-ternary original, including pure3-powers withn=1, costs at most

    H(t)=(1/2)sum_(D subsetQ)beta_D F_(D,2)(t).          (RC5)

No ternary height cutoff enters(RC5).

## 3. The finite null contract and nonnegative remaining inventories

Choose one finite set S of shallow mixed numerical labels3^h n,0<=h<=2,n>1. The hypothesis is

    lambda(G intersect actual_original_m)=0
    for every PRESENT original whose labelm belongs toS.          (RC6)

Absent labels are free. This permits actual cylinder containment in the reference excluded union, or nullity caused by the actual pure survivor laws. It does not require the reference exclusions themselves to be actual originals.

For each supportD, subtract the selected numerical contributions from its complete budget:

    R_(D,h)=beta_D-sum_(3^h n inS,supp(n)=D)c_n,         (RC7)

forh=1,2 and nonemptyD, and forh=0 when|D|>=2. Set every otherR_(D,h)=0. Because S is finite, its numerical labels are distinct and(RC4) is the complete positive inventory, every coefficient in(RC7) is nonnegative.

All unselected shallow originals have arbitrary phases. Union bounding their intersections with G, and then charging(RC5), gives

    lambda(U)>=L_S(t)
      :=M(t)-H(t)-sum_(D,h=0,1,2)R_(D,h)F_(D,h)(t),    (RC8)

where U is the actual old-head survivor. Overlaps among charged originals are allowed; the inequality does not assume their independence. The actual product source determines the same t in every term.

The contract is nonempty. To realize all selected labels explicitly, a singleton-support3q^j or9q^j cylinder may choose its ternary root and q-digit inside the corresponding reference3q exclusion. A selected n with at least two prime factors may choose phase2 in every supported first digit, placing it inside a referencepq exclusion. Higher digits can then be chosen consistently for each fixed numerical label. This supplies sufficient examples, not a claim that arbitrary shallow phases satisfy(RC6).

## 4. Why exactly128 parameter vertices suffice

Fix all t coordinates except one. A_D and B_D are affine in the remaining coordinate. F_(D,0) and M are affine; F_(D,1) and F_(D,2) are maxima of two affine functions and hence convex. Equations(RC5),(RC7),(RC8) subtract those convex functions with NONNEGATIVE coefficients. Thus L_S is concave in each coordinate separately.

For one coordinate between its endpoints, concavity bounds the value below by the linear interpolation of the endpoint values, hence by their minimum. Apply this successively to the seven coordinates:

    L_S(t)>=min_(epsilon in{0,1}^7)L_S(epsilon_q u_q).   (RC9)

This argument does not require joint concavity or assume that the all-upper vertex is worst. All128 vertices must be checked. Writing selected-label savings separately with positive coefficients multiplying maxima can conceal the sign argument; the residual inventory form(RC7) makes it valid.

For the specific weights a=1/3,b=1/9, A_D>=(1-u5)B_D=(11/15)B_D. Therefore the maxima in(RC3) select root1/its leaves throughout the cap box, and the bound is in fact multiaffine. The more general separately concave form allows other fixed laws without changing sources between terms.

## 5. A23-label contract for one fixed law

Take(a,b)=(3/16,5/24) and select these23 original numerical labels, displayed in their decreasing all-upper-vertex credit order:

    15,21,45,33,35,39,63,51,57,55,105,75,
    69,65,99,77,85,117,95,165,91,147,225.

The minimum of(RC8) over the128 vertices occurs at the all-upper vertex and is

    alpha23=16790988780569/557509082130000
           =approximately0.030117874880921987.           (RC10)

This is a uniform lower bound for one actual source satisfying(RC6), not a claim that a finite actual pure family attains every cap.

The phase-null conditions remain attached to the actual original cylinders after one common normalization. The23 slots need not constitute23 independent scalar equations, and the condition does not require all23 originals to occur.

The exact consumer also retains two fixed-law controls:

| One fixed ternary law | Selected labels | Certified source mass | Complete tail reserve |
|---|---:|---:|---:|
|(1/3,1/3,1/9,1/9,1/9)|52|0.037732951376369686|0.029808881486799128|
|(1/5,1/5,1/5,1/5,1/5)|23|0.025169544553722417|0.007831197000195887|
|(3/16,3/16,5/24,5/24,5/24)|23|0.030117874880921987|0.06553188936505805|

The displayed decimals are approximations to retained exact fractions. Each row uses its own fixed law consistently for the source, complete-query envelope and tail. The selected23-label sets in the last two rows agree, although their credit order differs. No continuous optimization over all weights is asserted.

## 6. Complete arbitrary queries and the same29/tail source

The complete-query rearrangement and continuation from [Report790](../750-799/790-shared-pair-deficits-admit-twenty-nine-at-a-depth-two-profile.md) and [Report734](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md) apply to every fixed law above. Put

    r=max(2a,3b),     v=max(a,b),
    Pr(J3>=1)=r,     Pr(J3>=e)=v3^(2-e) for e>=2,
    Pr(Jq>=e)=C_q/q^e,
    Z=product_(p in{3}unionQ)(1+Jp).

These independent nested runs describe only an auxiliary comparison law. Every complete actual query may choose an unrelated phase at each numerical label. The original source remains lambda, with mu=lambda restricted to U divided by its actual mass. If lambda(U)>=alpha>0, the complete query bound is

    B(mu)<=min_(h>=0)[h+E(Z-h)_+/alpha].                (RC11)

The exact hinge uses the FULL mean and only its small correction atoms:

    E(Z-h)_+=EZ-h+sum_(j<h)(h-j)Pr(Z=j),
    EZ=(1+r+3v/2)product_q C_q.

For the stated23-label law, r=5/8,v=5/24 andh=16 give

    B(mu)<=B*=approximately25.898885418565374<28.

Avoid actual pure29 originals by their normalized actual survivor law rho29. Restrict mu tensor rho29 to the actual remaining29 survivor without further normalization. This ONE submeasure has mass at least(28-B*)/27, approximately0.07781905857165276, and complete fourth-query envelopeK/alpha, where

    A4(q)=q(q^3+11q^2+11q+1)/(q-1)^4-1,
    K=[1+15r+216v]product_q[1+C_q A4(q)]
                         *[1+(28/27)A4(29)].           (RC12)

The unit query is included inB and excluded exactly once by pure29 conditioning. Queries may use old cofactor depths appearing only in29/tail originals. Those projections are not added as head forbidden classes.

Report734's complete tail withdelta2/7, growth21, cutoff3000 andell7 has

    tau=(21609/10240)(99/97)^21*3000/2999^4
          *sum_(j=0..21)21!/[(21-j)!21^j].

Every range and polynomial premise holds. The final same-source mass is at least

    (28-B*)/27-K*tau/alpha23
       =approximately0.06553188936505805>3/50.         (RC13)

The inherited analytic premise is the attributed Rosser--Schoenfeld prime-product estimate used in Report734. Every original is assigned once to its last outside prime, with its full earlier cofactor, phase and exponent. Thus all finite prime sets strictly above3000 are covered by the estimate; there is no numerical tail enumeration cutoff. Positive supported mass supplies an actual finite CRT survivor and hence an uncovered integer. The number3/50 is distorted mass, not a Haar-density claim of that size.

## 7. What the23-label minimality does and does not say

Fix the reference core, the weights(3/16,3/16,5/24,5/24,5/24), the intersection union bound(RC8), the fullbox reduction(RC9), and the complete hinge/quartic continuation. At the all-upper vertex, the credit from selecting a label3^h n is c_n F_(D,h)(u). The largest total credit fromk slots is obtained by choosing thek largest such numbers.

The verifier enumerates Q-smoothn<=5000 by direct integer factorization. Every omittedn>=5001 has credit at most product_q C_q/5001, since each core-intersection factor is at most1. This is below the23rd credit

    782770221599/85704035917500=approximately0.009133411434118534.

The finite ordering is therefore exact over all shallow numerical labels, without an exponent cutoff. With only22 selected slots, even the largest possible credit at this one vertex yields

    alpha22=46328154662663/2207735965234800
           =approximately0.020984463446803454.

For this fixed law, the full-tail positivity gate is

    min_(0<=h<28)[E(Z-h)_++27Ktau]/(28-h)
       =approximately0.025677092080555696.             (RC14)

It suffices to test integer thresholds: Z is integer-valued, so the hinge is affine on each unit interval and the ratio in(RC14) is monotone or constant there. Thresholdsh>=28 cannot supply a positive29 reserve; negative thresholds give no improvement over0.

Since alpha22 is below the gate, no22-label selection can certify positivity through this fixed fullbox method. The23-label selection passes all128 vertices, so23 is the exact minimum FOR THIS CERTIFICATE. The same argument applied separately to the other two retained laws certifies their respective52- and23-label minima. It does not compare every possible law.

The all-upper point need not be realized by a finite actual pure family. Failure at that point is a limitation of the stipulated fullbox certificate, not a covering family or an impossibility theorem for better source analysis. Different weights, reference cores, exact unions, actual source constraints or query estimates can change the minimum. No universal lower bound of23 on necessary phase conditions is asserted.

## 8. Reproducible verification and open scope

The [standalone exact consumer](../../../frontier/cover-geometry/refined-capped-source/retained_core_phase_union.py), [certificate](../../../frontier/cover-geometry/refined-capped-source/retained_core_phase_union_certificate.json) and [result](../../../frontier/cover-geometry/refined-capped-source/retained_core_phase_union.json) retain all128 source bounds for each law and every complete-query and tail constant. The program reconstructs core probabilities by a Bernoulli count recurrence, independently enumerates numerical labels, uses divisor convolution for subthreshold product atoms, and uses the complete Eulerian fourth-moment formula. Every decision uses fractions; floating point appears only in display fields.

Finite controls check the32768 Boolean hit-removal comparisons, all residual inventory signs, the selected-credit identity on all128 source vertices, and exact coordinatewise midpoint inequalities. The three-case replay completes55742 explicit checks. Normal and optimized runs exit0, as do both replays after relocating the three artifacts together to an independent directory. Eleven forged certificate/result controls are rejected with exit1, including a22-label contract below the gate and a changed retained source mass.

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/retained_core_phase_union.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/retained_core_phase_union.py
```

Default execution recomputes and compares the adjacent retained result. Explicit `--certificate`, `--result` and `--write-result` paths support replay or regeneration. All checks remain active under optimization. An independent weight/source computation agrees on all128 source vertices and the exact query/tail constants for the stated23-label law. These controls support the implementation; the universal conditional proof is(RC1)-(RC14). The program does not inspect an arbitrary original family or discharge its actual phase-null hypothesis(RC6).

The theorem retains Report800's finite phase-null interface and admits arbitrary higher ternary powers. It strengthens the source bound by accounting for the core once and keeping its actual hit probabilities common across all terms. It does not remove the finite phase contract, admit the excluded intermediate primes, replace the analytic tail premise, or settle unrestricted Erdős#7.
