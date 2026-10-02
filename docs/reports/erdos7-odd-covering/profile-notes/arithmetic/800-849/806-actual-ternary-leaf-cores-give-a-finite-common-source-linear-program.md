# Actual ternary-leaf cores give a finite common-source linear program

Allowing the two or three leaves in one ternary root to have different decreasing Boolean cores retains an actual distinction that a root-only core loses. For the fixed originals 0 mod3, 1 mod9, 10 mod15 and20 mod45, one uniform five-leaf source has surviving core mass22/25. Any core constant across the leaves of each root, on that same source and disjoint from those originals, has mass at most4/5.

For any fixed choice of five decreasing Boolean cores and any fixed selected shallow numerical inventory, the complete source lower bound remains separately concave in every common first-hit probability. With seven nonternary primes its128 cap-box vertices suffice. At a fixed complete-query hinge threshold, existence of one weight vector making this full-box certificate admit29 and a certified complete prime tail is exactly a finite linear-program feasibility question with positive objective value. Its variables keep one weight vector across all vertices and include the actual selected-cylinder nullity restrictions.

A fixed eight-prime example with a genuine3q/9q root conflict also passes the continuation: with empty old pure-q inventories, the stated leaf core and weights retain distorted mass greater than3/25 after arbitrary29 originals and every finite prime tail strictly above1600. All unselected mixed old labels and all higher ternary heights remain arbitrary. The same fixed weights do not pass that continuation using the generic full-box bound for arbitrary old pure-q inventories.

These are ordinary conditional arguments and exact rational controls. No LP optimum, universal successful choice of cores or weights, new Lean verification, or solution of unrestricted Erdős#7 is asserted.

## 1. What is reused and what changes

[Reports791](../750-799/791-uniform-shared-deficits-lower-depth-two-tail-cutoff-to1300.md) and[792](../750-799/792-optimal-fixed-leaf-weights-admit-the-complete1200-tail.md) already use common root/leaf roles, complete numerical inventories, separate concavity and fixed-law query comparisons. [Report795](../750-799/795-retained-leaf-bounds-admit-twenty-nine-at-both-opposing-profiles.md) retains actual nonnegative leaf survival while keeping the original full source for queries; [Report796](../750-799/796-coherent-fractional-allocations-obstruct-the-clipped-fixed-weight-template.md) limits its fixed-weight relaxed template. Those completed colour domains are not substituted for actual original phases here.

[Report794](../750-799/794-actual-prefix-orbits-make-all-height-source-search-sparse.md) already gives an exact actual-prefix-orbit query LP for a specified finite family, retaining every numerical label. It does not supply the full-inventory, product-source cap-box certificate below or a uniformly positive optimum. The present LP is a more restricted source certificate with only five source weights; it does not claim a new general principle of convex optimization.

The core-intersection charge and the sign-preserving residual-inventory form come from [Report801](801-retained-core-intersections-reduce-shallow-phase-contracts-to23-labels.md). Here each ternary leaf may have its own core, rather than inheriting one of only two root responses. This keeps the literal leaf affected by a9q original when a3q original for the same q lies in the other root.

## 2. Five fixed decreasing cores on one product source

Use the normalized ternary leaves

    L=(4,7,2,5,8) mod9,
    roots A={0,1}, B={2,3,4}.

Let Q be the finite set of nonternary old primes, normally(5,7,11,13,17,19,23). For each q use the actual normalized survivor law lambda_q of its pure-q originals. Choose one common reference c_q modq and let

    E_q={x_q=c_q modq},
    t_q=lambda_q(E_q),
    0<=t_q<=u_q=C_q/q,
    C_q=(q-1)/(q-2).

Choose nonnegative weights w_l summing to1. The single full source is

    lambda_w=lambda3,w tensor product_(q inQ)lambda_q,            (LC1)

where the ternary suffix above depth2 is Haar. Each leaf l has a fixed decreasing set G_l subset{0,1}^Q: if b is accepted and b'<=b coordinatewise, b' is accepted. Set

    G={(l,x): (1_(E_q)(x))_(q inQ) belongs to G_l}.

Every reference and every G_l is fixed before evaluating losses and queries. There is no separate choice for a numerical label, a cap-box vertex or a query.

For D subsetQ let

    A_(l,D)(t)=E[1_(G_l)(B with all coordinates inD set to0)],   (LC2)

where B has independent Bernoulli coordinates of probabilities t_q. This is the actual product-source response with queried coordinates removed. It is a separately affine polynomial in t, with values in[0,1]. In particular

    lambda_w(G)=M(t,w)=sum_l w_l A_(l,empty)(t).                 (LC3)

If an actual Q-smooth cylinder has numerical label n>1 and supportD, it fixes the first-hit bits inD. Decreasingness gives, on every compatible ternary leaf,

    lambda_Q(actual_n intersect G_l)
       <=(C_D/n) A_(l,D)(t),    C_D=product_(q inD)C_q.         (LC4)

This uses the cylinder's probability onD and the independent coordinates outsideD. It does not require simultaneous attainment of the cylinder cap and the core response.

## 3. The whole numerical inventory, including all heights

For a supportD define

    F_(D,0)=sum_l w_l A_(l,D),
    F_(D,1)=max_(R in{A,B}) sum_(l inR)w_l A_(l,D),
    F_(D,2)=max_l w_l A_(l,D).                                 (LC5)

An actual original3^h n has core-intersection mass at most(C_D/n)F_(D,h) for h=0,1,2. If h>=3, its bound is

    (C_D/n)3^(2-h) F_(D,2).                                    (LC6)

Height0 permits every retained leaf; height1 selects one whole root; height2 selects one leaf; deeper heights further select its Haar suffix. These alternatives come from that original's globally fixed phase.

The complete cofactor budget is

    beta_D=sum_(supp(n)=D)C_D/n=product_(q inD)1/(q-2),
    beta_empty=1.

Since sum_(h>=3)3^(2-h)=1/2, every higher-ternary original, including pure powers3^h, is charged by

    H_high=(1/2)sum_(D subsetQ)beta_D F_(D,2).                   (LC7)

Fix a finite setS of distinct shallow mixed numerical labels3^h n, h<=2,n>1. At h=0 require|D|>=2, because pure-q originals are already removed. Subtract each selected label exactly once from its complete numerical inventory:

    R_(D,h)=beta_D-sum_(3^h n inS, supp(n)=D)C_D/n.              (LC8)

Use this expression for h=1,2,D nonempty and for h=0,|D|>=2; set all otherR to0. These coefficients are nonnegative, even when a selected label is absent from the actual family.

If every selected actual cylinder is null on the same G under lambda_w, then for the full actual old survivorU,

    lambda_w(U)>=L(t,w)
      :=M(t,w)-(1/2)sum_D beta_D F_(D,2)
              -sum_(D,h=0,1,2)R_(D,h)F_(D,h).                 (LC9)

This is a lower bound obtained by charging intersections insideG; U itself need not equalG. All unselected actual phases remain arbitrary. No numerical labels or deeper exponents are dropped merely because they were absent from a finite search.

## 4. Nullity is a condition on the actual selected cylinders

For a present selected original m=3^h n with actual phase a_m, let

    H_m={q in supp(n): a_m=c_q modq}.

A retained leaf l is compatible if its literal residue satisfies l=a_m mod3^h. If the actual nonternary n-cylinder has positive lambda_Q mass, then its intersection withG on that leaf is null exactly when

    w_l=0 or 1_(G_l)(H_m)=0.                                  (LC10)

Indeed, if the fixed hit pattern is rejected, every larger outside-hit pattern is rejected. If it is accepted, the event that all coordinates outsideD miss is accepted and has positive probability: t_q<=u_q<1. Independence and positive cylinder mass then give a positive intersection whenever w_l>0.

Thus each incompatible selected/leaf incidence gives the linear restrictionw_l=0. It must be included when optimizing weights. Alternatively one can verify pointwise disjointness on every leaf in advance, so these restrictions are empty. An absent selected original or one already null under its actual pure survivor laws supplies no restriction. When the latter nullity has not been established, pointwise disjointness or the zero-weight restriction is the valid uniform requirement.

It is not valid to optimize over every weight vector while carrying forward a selected-null hypothesis that held only because some old weights vanished. The actual modulus, phase, shared reference and compatible leaf determine the restriction.

## 5. Separate concavity and the exact finite LP

Fix the cores, references, selected inventory and one weight vector. In any one t_q, each A_(l,D), M and F_(D,0) is affine. The root and leaf maxima inLC5 are convex. Every coefficient multiplying their negative inLC9 is nonnegative. Hence L is concave in each t_q separately, and

    L(t,w)>=min_(epsilon in{0,1}^Q)L(epsilon_q u_q,w).           (LC11)

For seven primes there are128 vertices. They are not asserted to be jointly attainable by finite actual pure families. Their use is a sufficient full-box certificate.

Fix an integer hinge threshold0<=h<28 and a nonnegative rational certified tail coefficientT. Let a_(epsilon,l,D) be the rational numbersA_(l,D)(epsilon u). Use one shared set of variables

    w_0,...,w_4, alpha, r, v,

and separate root/leaf epigraph variables z_(epsilon,D),y_(epsilon,D) at EACH vertex and support. The source constraints are

    w_l>=0, sum_l w_l=1;
    w_l=0 for every required incidence fromLC10;
    0<=alpha<=1, 0<=v<=r<=1;
    r>=w0+w1, r>=w2+w3+w4, v>=w_l for everyl;

    z_(epsilon,D)>=sum_(l inA)w_l a_(epsilon,l,D),
    z_(epsilon,D)>=sum_(l inB)w_l a_(epsilon,l,D),
    y_(epsilon,D)>=w_l a_(epsilon,l,D) for everyl;
    0<=z_(epsilon,D)<=1, 0<=y_(epsilon,D)<=1;

    alpha<=sum_l w_l a_(epsilon,l,empty)
      -sum_D R_(D,0)sum_l w_l a_(epsilon,l,D)
      -sum_D R_(D,1)z_(epsilon,D)
      -sum_D [R_(D,2)+beta_D/2]y_(epsilon,D)
        for EVERYepsilon.                                    (LC12)

Epigraph variables are not shared between vertices. Sharing them would impose an unnecessarily larger simultaneous maximum and change the certificate. The weights, alpha, r andv ARE shared: choosing one weight vector independently at each vertex would change the required existential-before-universal quantifier.

The objective is given below. The conversion is exact for this specified certificate. From a weight vector, choose epigraphs at their actual maxima to recover everyL(epsilon u,w). Conversely any feasible epigraphs are at least those maxima, so their nonnegative loss coefficients make each right-hand side no larger than the trueL. Thus a feasiblealpha is valid for that same weight vector throughout the box.

## 6. The full hinge and fourth moment are affine in r andv

For the one full source lambda_w, the actual root and leaf caps are

    r0=max(w0+w1,w2+w3+w4), v0=max_l w_l.

Use the complete auxiliary ternary run with tailsr at depth1 andv3^(2-e) at depthe>=2, where0<=v<=r<=1. Let W be the product of(1+J_q) over q inQ, withPr(J_q>=e)=C_q/q^e. The full query hinge is

    H_h(r,v)=E[((1+J3)W-h)_+]
            =H0_h+Hr_h r+Hv_h v.                              (LC13)

The coefficients are nonnegative. WithPhi(j)=E[((1+j)W-h)_+], tail summation gives

    H0_h=Phi(0),
    Hr_h=Phi(1)-Phi(0),
    Hv_h=sum_(e>=2)3^(2-e)[Phi(e)-Phi(e-1)].

Every difference is nonnegative. The sum converges because W has finite mean andPhi has at most linear growth. For exact rational evaluation use the complete mean and only the finite correction:

    H_h=EW(1+r+3v/2)-h
         +sum_(k<h)(h-k)Pr((1+J3)W=k).                         (LC14)

The ternary factor1+J3 has mass1-r at1, r-v at2, and2v/3^(d-2) at integerd>=3. Finite divisor convolution with the nonternary run probabilities computes every correction term. This is a full-height identity, not a truncation of the high-query tail.

With

    Kq=product_(q inQ)[1+C_q A4(q)] *[1+(28/27)A4(29)],
    Kbase(r,v)=Kq(1+15r+216v),                                (LC15)

the same complete-query comparison and actual pure29 conditioning used in801 give a post29 mass at least(28-h-H_h/alpha)/27 and a complete fourth-query boundKbase/alpha. No separate source is chosen for these two bounds.

If T is a valid common fourth-moment tail allowance, positivity is therefore

    epsilon=(28-h)alpha-H0_h-Hr_h r-Hv_h v
                        -27Kq(1+15r+216v)T>0.                 (LC16)

Maximize this LINEAR objective underLC12. Reducingr,v to the actual capsr0,v0 preserves feasibility and cannot decrease the objective because its coefficients inr,v are nonpositive. Thus using epigraph root/leaf caps neither adds false certificates nor loses a positive certificate. For any feasible point with epsilon>0, alpha>0 and the final distorted mass is at leastepsilon/(27alpha).

Conversely, if the fixed cores and selected inventory admit a weight vector with the full-box source bound and positive fixed-hinge gate, choosealpha=min_epsilon L(epsilon u,w), the exact maxima for every epigraph andr=r0,v=v0. This gives a feasible LP point with positive objective. This equivalence concerns the stated sufficient method; it does not identify the actual survivor optimum over all probability laws.

For the examples, T at1600 is the SOURCE-INDEPENDENT allowance of [Report804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md):

    T1600=4301685063112470380207/10^30.

The consumer rebuilds its complete179-prime recursion from1601 through2999, rounding upward at each step, and appends the full Report734 analytic tail above3000 withdelta2/7. That transfer depends only on a current common fourth-query bound, not on801's particular initial source. For comparison, directly applying Report734 HM15 atB=1600,ell=6 gives the larger allowance approximately1.0813132373953766 times10^(-8). The two coefficients must not be conflated.

## 7. A literal3q/9q root conflict

Take the four actual originals

    0 mod3, 1 mod9, 10 mod15, 20 mod45.

The15 original is(x mod3=1,x mod5=0); the45 original is(x mod9=2,x mod5=0). Their globally fixed phases put the3q condition on the short root and the9q condition on one leaf of the other root.

Use uniform weights1/5 and Haar at5, withE5={x mod5=0}. The fixed leaf cores are

    G4=G7=G2={no5 hit},
    G5=G8={all first-hit states}.                              (LC17)

These cores exactly match the actual survivor inside the five-leaf source. In the period45 there are25 source atoms of mass1/25. The15 class removes two atoms and the45 class removes one different atom, leaving22/25.

A core constant across the leaves of each root must exclude the5-hit on the entire short root to avoid15. To avoid45 on the positive-weight leaf2 it must also exclude that hit on the whole long root. Its mass is therefore at most4/5. The leaf-dependent core retains the two valid atoms on leaves5 and8 with5-hit, a strict gain2/25. Every class and reference stays fixed throughout this comparison.

For the complete selected inventoryS={15,45}, still using the universalC5=4/3, LC9 gives

    L(t)=61/75-(3/5)t,
    min_(0<=t<=4/15)L(t)=49/75.                               (LC18)

The full-inventory mass bound is smaller than the actual22/25 because it also pays for every unselected allowed numerical label and higher ternary power. Its finite LP with fixedh=2 has a positive gate. This is a consistency instance, not a claim that the four-class family was previously an open noncoverage problem.

If one forgets the45-to-leaf2 incidence and leaves that leaf's core unrestricted, LC10 imposesw2=0. The original uniform weights violate this constraint; a purported LP that omits it would treat a positive selected intersection as free.

## 8. The same distinction gives an eight-prime continuation

Take the literal25-original family in [Report803](803-common-reference-phases-and-five-leaf-weights-do-not-remove-the-phase-obstruction.md), changing ONLY the original of modulus45 from40 mod45 to20 mod45. Thus all its nonternary prime-power phases are still0; every ternary original remains on the short root except this45 class, which is on leaf2. The actual moduli stay distinct, odd and nonunit. Use common referencesc_q=0 and

    w=(1/4,1/4,1/6,1/6,1/6),
    G4=G7={zero hits inQ},
    G2={at most one hit inQ, and no5 hit},
    G5=G8={at most one hit inQ}.                            (LC19)

Every selected no3 class requires at least two hits and is excluded by every core. Every selected short-root class requires a hit and is excluded there. The selected45 class requires the5-hit on leaf2 and is excluded byG2. These are pointwise checks of the actual phases; no relaxed joint-colour assignment is used.

When all old pure-q inventories are empty, the common actual vector ist_q=1/q. Keeping the same inherited cylinder constantsC_q, the complete residual-inventory bound is

    alpha_Haar=102428997125209/2365431391323000
              =approximately0.04330245954329703.              (LC20)

At the fixed thresholdh=16, the complete query bound is approximately23.18771626004864. The same mass/quartic source followed byT1600 gives

    final distorted mass>=approximately0.124532869373502
                         >3/25.                              (LC21)

The larger direct analytic allowance at1600 would instead give approximately0.04324755555762356>1/25; LC21 uses the explicitly reconstructed804 finite-prime bridge. The ordinary analytic prime-product premise remains inherited in both calculations.

Consequently the fixed conflicting-phase originals may be extended by arbitrary unselected mixed head originals, arbitrary higher ternary powers, arbitrary29-ending originals and any finite set of primes above1600. Old pure-q inventories must remain empty for this Haar-vector statement. Primes31 through1600 remain excluded. The bound is distorted mass, not a Haar-density claim of the same size.

With arbitrary actual pure-q survivor laws, the same fixed weights and cores have the uniform128-vertex head bound

    alpha_box=10616394331387/1736855217405000
             =approximately0.006112423318305563,

with minimum at the all-upper vertex. This is positive for the old head but gives a negative fixed-hinge continuation gate. That is failure of this one certificate under these weights, not a covering family or an all-weight LP infeasibility result. The integer2602750151 avoids all25 displayed actual originals, and is checked directly against their literal phases.

## 9. Paying selected union leakage requires its actual information

If selected cylinders are not null, the valid correction toLC9 is the actual union masslambda_w(G intersect union_(m inS)C_m), counted once. The five-core construction alone does not make that quantity a function of the first-hit vector t.

For example retain the same uniform five-leaf ternary source and referenceE5={0 mod5}. In one actual family the only pure5 original is1 mod25; in another it is6 mod25. The respective pure-survivor laws are uniform on the other24 residues. Both have

    t5=5/24.

For the fixed selected mixed original1 mod75, whose ternary root is1 and whose5-prefix is1 mod25, the actual source masses are respectively0 and1/60. Both sets of original numerical labels are{3,9,25,75}, with the same pure3/9 anchors. Thus identicalt does not determine deep selected leakage or even whether its positive-weight leaf needs a nullity restriction.

One may retain more actual prefix observations or supply a valid uniform leakage envelope. If the entire selected union is actually measurable in the retained leaf/Boolean-hit fields, its probability has an exact multiaffine expression and that particular subtraction can be handled accordingly. Arbitrary actual shallow labels with higher nonternary powers or unrecorded phases do not satisfy this condition automatically. No general128-vertex result for such a leakage correction is claimed here.

## 10. Exact controls and the remaining proof obligation

The [standalone consumer](../../../frontier/cover-geometry/refined-capped-source/leaf_core_linear_bridge.py) reconstructs the Boolean response polynomials by an integer subset transform, checks every core is decreasing, computes complete remaining numerical inventories, derives the actual zero-weight incidence constraints, and evaluates the exact minimal epigraphs at every vertex. The hinge coefficients use the complete mean and finite divisor convolution. No optimizer supplies the retained arithmetic and no optimum is asserted.

The [certificate](../../../frontier/cover-geometry/refined-capped-source/leaf_core_linear_bridge_certificate.json) contains both actual examples, their literal selected phases, fixed weights, shared references, core truth tables and fixed thresholds. The [result](../../../frontier/cover-geometry/refined-capped-source/leaf_core_linear_bridge.json) contains the source vertices, hinge coefficients, common mass/quartic continuation and the literal45-period survivor list. The calculation performs1381 explicit checks. Normal and optimized replays pass after relocating the program and data to paths containing spaces. Fifteen forged inputs are rejected in each mode, including illegal cores, omitted45 leaf incidence, altered actual phases, duplicate numerical labels, invalid weights or thresholds and forged source, hinge, tail or result data.

```sh
python3 -I -S -B leaf_core_linear_bridge.py \
  --certificate leaf_core_linear_bridge_certificate.json \
  --result leaf_core_linear_bridge.json
python3 -I -S -B -O leaf_core_linear_bridge.py \
  --certificate leaf_core_linear_bridge_certificate.json \
  --result leaf_core_linear_bridge.json
```

Both data paths are explicit; the consumer needs no repository import or working-directory convention. Use --write-result in place of --result to regenerate its exact output.

The new finite interface is useful only when its selected-null constraints and positive gate can be supplied for the actual family. A uniform proof would still need to construct appropriate actual cores and a SINGLE feasible weight vector with a positive objective for every allowed phase pattern, or replace the insufficient observations and estimates. The LP conversion does not establish that uniform existence statement.
