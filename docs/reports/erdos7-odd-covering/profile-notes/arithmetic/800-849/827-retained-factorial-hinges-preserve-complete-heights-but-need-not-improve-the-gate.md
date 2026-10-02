# Retained factorial hinges preserve complete heights but need not improve the gate

A complete second-factorial query envelope gives a direct hinge bound on the retained measure, with the same survivor denominator used by its head and fourth moment. For every fixed complete single query layout and integer threshold `h>=1`,

    integral (N-h)_+ dmu <= F2/[2(2h-1) alpha].

The complete coefficients are explicit, nonnegative and compatible with Report820's fixed-cell interpolation. This changes the full-product-hinge interface obstructed by [Report824](824-free45-phase20-has-a-live-cell-certificate-while-short-leaf-phases-obstruct-h16.md) and [Report826](826-one-finite-pure-family-obstructs-every-kernel-in-the-h16-comparison.md), but is not an automatic numerical improvement.

For one fixed rational phase31 candidate at corner C, the new h16 gate is `-0.327906096733674...`, compared with `-0.18656449487411977...` under the old hinge. An exact algebraic criterion further proves that this same candidate fails every useful integer threshold `1<=h<=27`, without scanning thresholds. These failures concern one candidate at one source point, not every retained kernel, an actual covering, or unrestricted Erdős #7.

The bridge and computations are ordinary conditional mathematics with exact rational checks, not Lean results. The unchanged prime support is `{3,5,7,11,13,17,19,23,29}` together with an arbitrary finite set of primes strictly above1600; primes31 through1600 remain excluded. Report804's full-tail contract and inherited Rosser–Schoenfeld analytic premise remain in force.

## Reused mathematics and the retained-source connection

The applicable existing results are:

- [Report108](../../065-128/108-a-complete-second-factorial-tail-improves-four-quadratic-costs.md), Sections1 and4: expand a factorial expression into pairs of distinct numerical labels before applying positive LCM-cylinder caps. Its scope is an older saturated357 source, but its accounting principle is exactly the one required here. It explicitly rejects subtracting unrelated upper moment bounds.
- [Report592](../550-599/592-joint-second-moment-extends-cubic-tails-to-ten-primes.md), Section2: the number of ordered divisor pairs whose coordinatewise maximum exponent is `e` is `product_p(2e_p+1)`. Compatible pairs meet in one LCM cylinder; incompatible pairs contribute zero. Its source and continuation differ from the present retained kernel.
- [Report589](../550-599/589-normalized-joint-hinges-close-the-shallow-two-phase-slice.md), Sections1–4: uniform single-layout hinge contracts belong to one normalized actual law; full heights follow by finite boxes, exact geometric remainders and monotone convergence. Its four-hinge forward construction is not the present table or a license to import its constants.
- [Report820](820-queried-colour-capacities-sharpen-complete-head-and-moment-bounds.md) CC1–CC7: one retained table and one product source provide common-colour capacity envelopes, a complete three-depth-type inventory, and the complete retained fourth-query moment.
- [Report815](815-retained-source-moments-have-a-three-point-common-kernel-obstruction.md) Section3, Report801 RC12 and [Report804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md): the 29-ending stage needs a uniform bound on every single complete query; the following tail uses the full four-layout moment of that same source. Both numerators are divided by the same retained survivor mass. Their transfer does not require that the single-query bound be supplied by a full-product hinge.

Thus the ingredients are established methods. The present bridge is the direct complete second-factorial envelope for the current Report820 retained source, followed by a valid integer hinge majorant. No novelty claim is made.

## 1. Exact integer hinge majorant

For every integer `n>=0` and integer `h>=1`,

    (n-h)_+ <= n(n-1)/[2(2h-1)].                         (FH1)

For `n<h`, the left side is zero and the right side is nonnegative. For `n>=h`, multiplying by the positive denominator leaves

    n(n-1)-2(2h-1)(n-h)
      =(n-(2h-1))(n-2h)>=0.

The two roots are adjacent integers, so the product cannot be negative at an integer. Equality holds at `n=2h-1` and `n=2h`; `n=2h` has positive factorial value, so this is the smallest uniform coefficient multiplying `n(n-1)`. At `h=16` the denominator is62.

The integer hypothesis matters: at `n=2h-1/2` the multiplied difference is `-1/4`. FH1 is not asserted for arbitrary nonnegative reals.

## 2. Remove one global diagonal before applying any cap

Fix one finite complete numerical query layout, including the unit label. It assigns one globally fixed phase to each numerical divisor `d`; phases belonging to different labels need not be compatible. Write

    N(x)=sum_d I_d(x), I_d=1_[a_d mod d].

Then pointwise

    N(N-1)=sum_(d!=e) I_d I_e.                          (FH2)

A compatible pair is one cylinder of modulus `lcm(d,e)`; an incompatible pair contributes zero. If its maximum exponent vector is `t=(t_p)`, the full ordered exponent-pair count is

    product_p(2t_p+1).

There is exactly ONE diagonal exponent pair with that maximum vector: both labels equal its complete numerical modulus. Consequently the number of globally distinct pairs in the class is

    product_p(2t_p+1)-1.                                (FH3)

This is not `product_p 2t_p`: two labels can have equal exponents on one coordinate while differing on another. For maxima `(1,1)`, the correct count is8, not4.

Only after this combinatorial deletion is each remaining pair capped by the common cylinder envelope. No actual first-moment lower bound is needed and no upper first-moment estimate is subtracted from an independently bounded second moment. Different pairs may maximize different cylinder colours; applying a uniform cap pair by pair gives an upper bound and does not assert simultaneous attainment.

FH2 is for ONE layout. For two differently phased layouts, the same-label product need not be the single indicator, so one cannot replace the mixed diagonal by a first moment. The four-layout fourth-moment bound used later remains unchanged and does not need that deletion.

## 3. Complete retained coefficients

Use Report820's actual finite product source, one normalized leaf weight vector, and one genuine retained table `0<=u_l(s)<=w_l`. Let `F_(D,S,h)` denote its common-colour capacity envelopes, with a fixed live/dead pattern. Here `h=0,1,2` denotes no ternary condition, one root, or one leaf; it is distinct from the integer hinge threshold in FH1. The three-depth formulas apply when each positive colour exceeds its second-depth cap, as on Report816's actual structural cells.

For nonternary support `D` and shallow subset `S`, define

    B_(D,S)=product_(q in S) C_q/q
             product_(q in D outside S) C_q/[q(q-1)],
    V_(D,S)=product_(q in S) 3 C_q/q
             product_(q in D outside S) C_q[a2(q)-3/q],
    a2(q)=3/(q-1)+2/(q-1)^2
         =sum_(e>=1)(2e+1)q^-e.                          (FH4)

`B` counts one diagonal numerical label per maximum-depth vector; `V` counts all ordered pairs. The same cylinder cap carries one factor `C_q`, not two, because a compatible pair produces one cylinder.

The complete ternary ordered-pair factors are

    depth0: 1;
    depth1: 3;
    depth>=2: sum_(j>=2)(2j+1)3^(2-j)=9.

The corresponding one-diagonal-label factors are

    depth0: 1;
    depth1: 1;
    depth>=2: sum_(j>=2)3^(2-j)=3/2.

Applying FH3 within each complete depth class therefore gives

    integral N(N-1) dnu_u <= F2,

    F2=sum_(D,S) [(V-B) F_(D,S,0)
                  +(3V-B) F_(D,S,1)
                  +(9V-(3/2)B) F_(D,S,2)].              (FH5)

All coefficients are nonnegative. Locally the ratio of pair to diagonal factors is3 at depth1 and

    [a2(q)-3/q] / [1/(q(q-1))]=5+2/(q-1)

at depth>=2. Thus `V>=B>0`, including `D` empty, where `B=V=1` and the three coefficients are exactly `(0,2,15/2)`.

No selected-original deduction is made from this query-pair inventory. Arbitrary query phases at a selected numerical modulus need not equal its actual original phase. Selected nullity is already a condition on `u`; only the diagonal query pairs have been removed. Every nonternary type is retained, including empty support and pure types that do not carry a head-loss debit.

For seven nonternary primes the formula has all `3^7=2187` types. It sums every height; no finite exponent cutoff defines FH5. For an explicit exact remainder,

    sum_(e>=E)(2e+1)q^-e
      =q^-E[(2E+1)/(1-q^-1)+2q^-1/(1-q^-1)^2].           (FH6)

Finite boxes give FH5 first. All ordered distinct-pair terms are nonnegative and their complete cap series is finite, so monotone convergence gives the same bound for complete fixed layouts. Completing a partial layout by arbitrary fixed phases only increases the nonnegative factorial expression.

## 4. The same retained normalization and continuation

Let `U` be the complete actual old survivor,

    alpha=nu_u(U), mu=nu_u restricted to U / alpha.

When `alpha>0`, restriction can only decrease the nonnegative hinge and factorial integrals. FH1 and FH5 yield, uniformly over each single complete query layout,

    integral (N-16)_+ dmu <= F2/(62 alpha),
    integral N dmu <=16+F2/(62 alpha).                    (FH7)

This bound applies to the correlated retained law directly; no assertion that the retained law is a product is used. The fourth-layout envelope is the unchanged `K4/alpha`, where `K4` is Report820 CC7 for the same `pi,u,w`. Appending the actual pure29 law contributes its fourth-moment factor exactly once,

    T29=120361/74088.

The ordinary 29-ending union estimate and Report804 tail thus give final distorted mass at least

    12/27 - [F2/62+27 T29 T1600 K4]/(27 alpha).           (FH8)

Using the unchanged head lower bound `alpha>=L`, a sufficient numerator is

    G_fact=12 L-F2/62-27 T29 T1600 K4.                   (FH9)

Both debits are nonnegative. Hence `G_fact>0` would itself imply `L>0`, supply the positive normalization, and give the same-source mass lower bound `G_fact/(27L)`. The prime support, actual phase contract, complete tail and analytic premise are unchanged. Section6 evaluates FH9 for one fixed candidate; no optimization or uniform positive source-cell claim follows from the bridge.

## 5. Fixed-cell interpolation and a caution about combining bounds

For fixed `u,w`, Report820's envelopes are block-convex on each actual structural cell. FH5 has nonnegative coefficients, so `F2` is also block-convex. Thus FH9 is block-concave and product vertices suffice for one unchanged candidate on one such cell. This does not interpolate across dead/live changes or unrestricted depth breakpoints.

At a single source point, both the old full-product hinge and FH7 are valid with the same denominator; their minimum is a valid upper bound. However, choosing that minimum independently at different vertices changes the numerator to a maximum of two block-concave functions. Such a maximum need not be block-concave. A future whole-cell proof must keep one valid branch throughout the cell or prove an appropriate partition/transport argument; mere positivity of this pointwise minimum at vertices is insufficient.

## 6. One fixed rational phase31 candidate at C

Keep the literal actual family of Report824 with phase31 at modulus45 and all other24originals fixed. In particular, the anchors are0mod3 and1mod9 and all23selected numerical mixed labels remain present. Use ternary leaves `(4,7,2,5,8)` and weights

    w=(21173425,21173425,19217717,19217717,19217716)/10^8.

The [certificate](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/retained_factorial_hinge_certificate.json) contains all106positive retained entries. Every other entry is zero; the actual phase31 family forces711of960cells to vanish and leaves249permissible entries. The consumer checks all literal nullities, `0<=u<=w`, and the exact equality `sum w=1`.

The only evaluated source point is

    pi5=(4/15,4/15,7/15),
    piq(0)=(q-1)/[q(q-2)], q=7,11,13,17,19,23.

The complementary probability is `1-piq(0)`. These are corner C and the six upper live endpoints. This is an enclosing-source-cell endpoint, not an assertion of its finite actual realization. In particular, no new comparison at Report826's finite family is asserted here.

All shallow capacity multipliers are exactly1 at this point. The computation retains all2187nonternary depth types. Independently summing their closed complete first-, second- and fourth-moment coefficient products gives the same384support/ternary responses. Their equality is checked exactly; it does not discard any deep remainder or add a source point.

| Quantity | Exact computation, displayed in decimal |
|---|---:|
| Retained mass `M` | 0.4784474119263616… |
| Complete head lower bound `L` | 0.012657886704707326… |
| Complete fourth moment `K4` | 242106.91830558638… |
| Full-product hinge `H16` | 0.2927768847683014… |
| Complete factorial envelope `F2` | 26.915346170927048… |
| Retained factorial hinge `F2/62` | 0.4341184866278556… |
| Tail debit `T=27 T29 T1600 K4` | 0.0456822505623063… |
| Old h16 gate | −0.18656449487411977… |
| Factorial h16 gate | −0.327906096733674… |

The [result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/retained_factorial_hinge.json) stores the rational values and every support contribution. Replacing only the hinge changes the gate by exactly `H16-F2/62`, which here equals `-0.14134160185955422...`. The fixed-candidate success criterion `G_fact>0` therefore fails, and this factorial estimate is looser than the old hinge for this candidate. Validity of a bound does not imply that it is the smaller available bound.

The new gate is homogeneous in the retained table: scaling `u` within its legal range scales `L,F2,K4` together. The old full-product hinge remains constant when only `u` is scaled. At `u=0` the new gate is0, but the survivor denominator is also0. Thus the old strictly negative all-kernel bound cannot simply be relabelled as a strictly negative bound for the new comparison, and the zero table supplies no positive supported source.

## 7. The fixed candidate fails every useful integer threshold

For this same candidate at this same point, write

    T=27 T29 T1600 K4,
    G(h)=(28-h)L-F2/[2(2h-1)]-T,
    A=(55/2)L-T.

Put `t=h-1/2>0`. Algebra gives

    G(h)=A-Lt-F2/(4t)<=A-sqrt(L F2).                     (FH10)

The inequality is AM–GM. It bounds the displayed rational function for every real `h>1/2`; the factorial-hinge theorem is applied only at integer thresholds. No extension of FH1 to real-valued query counts or arbitrary real thresholds is used.

Exact arithmetic gives

    L>0, F2>0,
    A=0.30240963381714514...>0,
    L F2-A^2=0.2492398158241529...>0.                    (FH11)

Therefore `sqrt(L F2)>A`, so FH10 is strictly negative for every integer `1<=h<=27`. The checker verifies the two rational signs in FH11 and the exact defining identities; it does not enumerate candidate gate values at different thresholds. Thresholds at least28 cannot supply a positive reserve through this sufficient numerator with positive `L` and nonnegative debits.

FH11 depends on this fixed table and source. It gives no upper bound for another table, another source point, a conditional-cell hinge, or a different moment construction. The mathematical bridge remains valid; this diagnostic does not establish that its best possible gate is nonpositive.

## 8. Finite controls, independent checks and reproduction

The [standalone consumer](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/retained_factorial_hinge.py) uses only the Python standard library and the delivered certificate and result. It includes28,743 finite controls for the general bridge:8,576 integer hinge cases with exact gap and equality checks, the noninteger counterexample, ordered exponent-pair inventories on up to four axes, a control rejecting coordinatewise diagonal deletion, every one of the2187complete nonnegative coefficient types, complete geometric remainders, and a literal9-label layout on a225-point carrier. A two-layout control rejects replacing a mixed diagonal by one layout's first moment.

The consumer additionally rebuilds the phase31 literal nullities, complete head inventory, full old hinge, complete factorial and fourth moments, once-only29factor and full804tail. It compares fulltype and aggregated coefficients at C and verifies FH11. These finite controls check implementation and edge cases; the ordinary proofs above carry the full-height and all-layout quantifiers.

Independent checks reconstructed the bridge without reading its same-round derivation and then reconstructed the C quantities by a separate tensor calculation. All11scalar quantities, all384response/coefficient entries and all128support contributions agree exactly. These checks do not constitute Lean verification or enlarge the source/candidate scope.

From the artifact directory:

```sh
python3 -I -S -B retained_factorial_hinge.py
```

Normal execution performs38,229checks and compares the saved mathematical result without rewriting it. `--certificate` and `--result` accept explicit paths. Regeneration requires `--write-result --result <new-path>` and refuses to overwrite an existing result. Neither a solver nor the earlier floating LP output is required.

The reusable outcome is a complete retained-source factorial-hinge interface and its precise accounting conditions. The fixed diagnostic supplies an obstruction to rescuing this one candidate merely by changing the integer threshold. Improving the actual source estimate still requires another justified relation or construction; no further source point or candidate is included in this result.
