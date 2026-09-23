# Integer layer loads give core margins and an exact envelope boundary

An actual core supported on 5,7,11,13 has an original completion load strictly below 3/2 whenever at least one of four specified prime-height bounds holds. The ternary height and the other three prime heights are arbitrary finite values. A complementary result allows all four core heights to be arbitrary finite when the ternary height is at most five: the load is then below its finite-height completion threshold by more than 1/1000. The proofs reuse Chapter19's same-law profiles and integer-load inequalities. These are ordinary mathematical deductions with exact parameter controls, not Lean certifications or claims of public mathematical priority.

## 1. Original labels and the completion margin

Let

    Q=5^h5 7^h7 11^h11 13^h13,

with finite nonnegative heights. Take any original family having at most one residue alpha_d for each numerical modulus

    d=3^e a,   a|Q, a>1,   0<=e<=H,

where H>=1 is finite. Missing labels and arbitrary original phases are allowed. Pure powers of 3 are EXCLUDED from the completion load; their available mass is already accounted for by B_H below. Let S be the COMPLETE actual core avoid-set of the original e=0 classes. For a present label define its literal cofactor event

    C_(e,a)={x mod Q: x=alpha_(3^e a) mod a},
    ell_H(x)=sum_(present e>=1,a>1)3^(1-e)1_C_(e,a)(x),
    B_H=(3+3^(1-H))/2.

Suppose at least one of

    h5<=3,   h7<=2,   h11<=1,   h13<=1                 (CH1)

holds. Then S is nonempty and contains an actual point x with

    ell_H(x)<3/2-1/2100<B_H-1/2100.                    (CH2)

In particular, the probability mu_*=delta_x is supported on the actual core residual and has this completion margin. The result does not require a universal Gamma bound, original comparable-class disjointness, or a common ternary phase. Its S is the complete core avoid-set, not an arbitrarily chosen subset of that set.

## 2. One old law and two original layers

Choose any one successful strip in (CH1). Let A_p be the complete permitted positive-depth geometric sum on coordinate p: on its bounded axis of height h use

    A_p=(1-p^(-h))/(p-1),

and on each other axis use A_p=1/(p-1). These infinite sums only majorize the actual finite original inventory. Put

    delta_p^(m)=1-m A_p,  m=1,2.

Let V_p avoid the original e=0 pure p-power classes, let nu be uniform on the product V=product_p V_p, and write

    s=nu(S),    mu=nu(. | S).

Thus mu is uniform on the same complete actual S throughout. The finite/infinite P3--P5 profile recursion from [Chapter19](../../problem-details/19-five-prime-parent-envelopes-and-the-cofactor-allocation-barrier.md), KE1--KE7, supplies one-layer coefficients c(T), a lower bound f_1<=s, and two-layer survivor bound f_2. For clarity, its m-layer induction adjoins coordinate p using

    gap=1-m A_p R_old/delta_p^(m),
    c_new^(p)(T)=c_old(T without p)/gap
                 times [1/delta_p^(m) if p in T, else 1],
    f_new^(p)=f_old gap.                               (CH3)

Only positive gaps are admissible. Take the minimum coefficient over valid last-coordinate orders and the maximum survivor bound. Every order concerns the same uniform complete survivor law, so these choices do not mix independently optimized probabilities. R_old sums the minimum subset-cylinder cap over the complete permitted nonzero exponent tuples. The exact tail cells below evaluate this sum at unbounded axes.

For a nonzero exponent tuple v define

    u_v=min_(T subset supp(v)) c(T)/product_(p in T)p^v_p,
    z_v=product_(p in supp(v))[1/(delta_p^(1) p^v_p)],
    R(s)=sum_(v!=0) min(u_v,z_v/s).                    (CH4)

Every original cofactor layer has expected load at most R(s) under the SAME mu. The unit cofactor is absent from (CH4).

Let N be the union of ALL e=1 cofactor events. Its union with the old e=0 classes has numerical multiplicity at most two for each a>1. This remains true when its original labels use different ternary phases: an original modulus 3a occurs at most once. Consequently the two-layer calculation is valid for this full N, not merely for one ternary-prefix subfamily.

Define b_p=A_p/delta_p^(1), and let e_j(b) denote an elementary symmetric polynomial. The same old product law satisfies

    nu(S without N)>=C:=f_2 product_p[delta_p^(2)/delta_p^(1)],
    nu(N)<=U:=e_1(b)+2e_3(b).

The first estimate retains the actual ratio of new and old pure domains before taking lower bounds. The second combines the union of pure-coordinate events with all mixed-support costs; the second- and fourth-order terms cancel algebraically, so no four-prime label is omitted. Hence

    mu(N)<=beta(s):=min(U/s,1-C/s),    f_1<=s<=1.       (CH5)

These are the same couplings as KE3--KE7, with the specified bounded-axis sum retained.

## 3. Integer loads give an actual core point below 3/2

Let g(x) count the present e=1 cofactor events containing x, and let

    z(x)=sum_(present e>=2,a>1)3^(1-e)1_C_(e,a)(x),
    T_H=sum_(e=2,...,H)3^(1-e)=(1-3^(1-H))/2.

For H>=2 put h=z/T_H; for H=1 put h=0. Thus ell_H=g+T_H h, and under the one mu above,

    E g<=R(s),    E h<=R(s),    Pr(g>=1)<=beta(s).     (CH6)

The late expectation is a convex combination of original-layer expectations when H>=2; its value is zero when H=1. Define

    psi(x)=g(x)+h(x)+1_[g(x)>=1],
    G(s)=3-2R(s)-beta(s).

All three terms use the same actual point and the same probability, so

    E psi<=2R(s)+beta(s)=3-G(s).                      (CH7)

If G(s)>=kappa>0, some x in S satisfies psi(x)<=3-kappa<3. Since g is a nonnegative integer, g>=2 would imply psi>=g+1>=3. Thus this SAME point has g=0 or 1. Because 0<=T_H<1/2,

    2ell_H(x)=2g(x)+2T_H h(x)
              <=2g(x)+h(x)
               =g(x)+h(x)+1_[g(x)>=1]
               =psi(x)<=3-kappa.                     (CH8)

Hence ell_H(x)<=3/2-kappa/2. A uniform kappa>1/1050 proves (CH2), including H=1. Every expectation and union bound in (CH6)--(CH8) uses mu; the final Dirac law is chosen only after locating x.

## 4. Exact mixed-height envelopes

For an unbounded coordinate p, choose a cutoff L_p with

    p^(L_p+1)>=max_(T not containing p)c(T union {p})/c(T).

Beyond that cutoff, adding p to a minimizing subset cannot increase the cylinder cap. Every exponent tuple can therefore be grouped into finitely many cells: exact bounded exponents, and one geometric tail for each unbounded coordinate. If J is the tail support, both u_v and z_v have the SAME factor product_(p in J)p^(-v_p). Its sum is exactly

    product_(p in J)1/[p^L_p(p-1)].

In each such cell, z_v/u_v is constant. Thus (CH4) is an exact finite sum of terms min(A,B/s); its switches and the switch s=U+C in (CH5), together with f_1 and 1, partition the entire interval. On each piece G(s)=a+b/s, whose extrema occur at the endpoints. No infinite axis is replaced by a large finite height.

The exact results are:

| Bounded axis; other three arbitrary | Minimizing s | Minimum kappa of G(s) | Exact exponent cells |
| --- | --- | --- | ---: |
| h5<=3 | 9301/11515 | 1765/1841598 | 31 |
| h7<=2 | 3251/4018 | 420/35761 | 23 |
| h11<=1 | 266/327 | 1986/36575 | 15 |
| h13<=1 | 434/535 | 544/17577 | 15 |

All four kappa values exceed 1/1050. Each envelope has thirteen breakpoints, and every adjacent interval is checked through its exact a+b/s formula. The cell column counts the old full-profile envelope; the two-layer recursion can require a larger tail cutoff and uses its own certified cells.

For example, in the first row the unrefined envelopes and coupled constants are

    R_1=40553/37204,    R_2=10607/3392,
    C=3392/23265,      U=35789/46530.

These constants, all subset profiles, tail-dominance comparisons, and interval coefficients are retained in the parameter control. Substituting the table in (CH8) proves (CH1)--(CH2).

## 5. The exact success boundary of this envelope

Increasing an allowed height increases A_p and decreases delta_p^(m). Inductively in (CH3), R_old increases, gaps decrease, the admissible-order set shrinks, every profile coefficient increases, and each f_m decreases. All intermediate computations remain defined because the existing completely unbounded m=1 and m=2 profiles have a positive valid order for every subset.

Consequently C decreases and U increases. For each fixed s, all existing terms of R(s) increase and newly allowed exponent tuples contribute nonnegative terms. Both branches defining beta(s) increase. Meanwhile the interval [f_1,1] expands. The infimum of G therefore cannot increase with any height.

The smallest integer height vector outside (CH1) is (4,3,2,2). Its exact envelope has

    min G=-10914212547/30626143160140<0,
    minimizing s=82397006/101984519.

Its 179 exponent cells give this bound without enumerating its arithmetic period. Monotonicity now shows that the four strips in (CH1) are exactly the positive-gap success domain of THIS envelope. An outside height vector is a failure of this sufficient estimate, not an actual counterexample to the weighted core-margin statement or to noncoverage.

## 6. Arbitrary core heights with ternary depth at most five

There is a complementary conclusion with no restriction on h5,h7,h11,h13. Keep all original-label and actual-survivor definitions from section 1, but assume 1<=H<=5. Then some actual x in S satisfies

    ell_H(x)<B_H-1/1000.                              (CH9)

This uses the completely unbounded core envelope already supplied by Chapter19, rather than one of the four mixed-height envelopes. In the same uniform actual survivor law, E g<=R(s), E h<=R(s), and Pr(g>=1)<=beta(s) still hold. For every nonnegative integer g and 1<=B<=2,

    (B-g)_+ >= (B-1)(2-g)+(2-B)1_[g=0].

It is equality for g=0,1,2, and the right side is nonpositive for g>=3. With B=B_H=2-T_H and ell_H=g+T_H h, the positive-part inequality gives

    E(B_H-ell_H)_+ >= E(B_H-g)_+-T_H E h
                    >=2-R(s)-T_H(1+beta(s))
                    =:Delta_H(s).                    (CH10)

Chapter19's existing thirteen breakpoints and twelve interval formulas cover s in [79/99,1]. On each interval Delta_H(s)=a+b/s, so its minimum is attained at an endpoint. Substitution at H=5 gives

    min_s Delta_5(s)=844/633501>1/1000,
    minimizing s=79/98.

Since T_H increases with H and beta(s)>=0, Delta_H(s)>=Delta_5(s) for 1<=H<=5. Equation (CH10) selects one point satisfying (CH9); different layers do not select different points. At H=6 the minimum of this same unbounded envelope is -11738/1900503, again at 79/98. This marks failure of this sufficient estimate, not an actual arithmetic obstruction. It does not alter the exact G-positive domain in section 5, which concerns the stronger bound below 3/2 at arbitrary ternary height.

The control consumes the existing [Chapter19 parameter data](../../frontier/cover-geometry/k5_parent_same_law_envelope.json) and checks these finite-height substitutions on every inherited interval. It does not rebuild or duplicate the unbounded profiles. This is a consequence of the existing envelope and the integer inequality, not a new general profile theorem.

## 7. Reuse, composition, and remaining boundary

Chapter19 already supplies the profile recurrence, the coupled R(s),beta(s) framework, and the quantity 3-2R-beta in KE15--KE16. The integer-load inequality above is elementary. This application supplies the original weighted-core point guaranteed by the bounded-axis positive gap; it does not introduce a new general profile or hinge theorem. No bind-only Lean wrapper is needed.

[Chapter18](../../problem-details/18-five-prime-cores-with-tree-and-cactus-attachments.md) already excludes covering by the five-prime core, and [Chapter33](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md) supplies stronger noncoverage ranges with unrestricted large-prime tails. Those conclusions dominate a bare noncoverage corollary here. The additional interface is the quantitative, original-label completion margins (CH2) and (CH9), supported at an actual core point and directly usable as a prescribed marginal.

In particular [report453](453-prime-tail-conditioning-preserves-core-laws-at-unrestricted-support.md) can preserve mu_*=delta_x while adjoining any finite outside family meeting its cutoff B>=3^256 tau(Q)^4. Its bound 324 tau(Q)/B<3^(-250)<1/2100 leaves positive total completion margin under either (CH2) or (CH9). When using (CH9), the same H<=5 must bound the entire original family, including pure powers of 3 and outside labels, so the completion threshold B_H remains the same. The arbitrary-ternary-height composition uses (CH2). The cutoff still depends on the full tail head-divisor inventory Q and can grow with its unrestricted coordinate heights. These results do not remove that cutoff, treat arbitrary core inventories, or settle unrestricted Erdős #7.

Exact controls: [program](../../frontier/cover-geometry/core_completion_hinge_profiles.py) and [results](../../frontier/cover-geometry/core_completion_hinge_profiles.controls.json).


The actual arithmetic control uses Q=385, H=4 and 35 distinct original numerical moduli, with all three original ternary root phases present at e=1. The complete old survivor set has 219 points inside a 240-point pure-coordinate domain, so s=73/80. Under its one uniform law, the first-layer count has frequencies {0:129, 1:74, 3:15, 7:1}. The means are E g=42/73, E h=575/949 and Pr(g>0)=30/73; the parameter envelopes are evaluated at this actual s before applying the point selection. The selected point x=29 has original weighted load 1/27.

The program also checks the integer positive-part identity, including the excess E(g-2)_+=20/219, and all 17739 complete CRT words above those 219 survivors. For each core point, three times the average literal original congruence-hit count over its ternary fibre equals ell_H(x). These finite controls check the original-label interpretation and common-law bridge; they do not replace the all-height proof or enumerate all residue choices.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/core_completion_hinge_profiles.py
```
