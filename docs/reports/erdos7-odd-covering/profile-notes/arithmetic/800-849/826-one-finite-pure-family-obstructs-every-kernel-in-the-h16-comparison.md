# One finite pure family obstructs every kernel in the h16 comparison

One explicit family of 53 pairwise distinct odd nonunit originals makes the specified h16 comparison strictly negative for every legal leaf-weight vector and categorical retained table, including choices adapted to this actual family. Its bound is strictly below `-4/25`. The family uses the selected mixed phase `31 mod45` and pure-prime combs of depth exactly four.

This is an obstruction to the inherited complete head-cap, full-source hinge and capacity-aware retained-source fourth-moment comparison. It is not a covering family: the integer 4 avoids all 53 originals. The result uses ordinary proofs and exact rational replay; it is not a Lean result.

## 1. The fixed comparison and its uniform quantifiers

[Report824](824-free45-phase20-has-a-live-cell-certificate-while-short-leaf-phases-obstruct-h16.md) supplies an exact weak-dual bound at its categorical point C. Its nonzero source-dependent rows belong only to C, with the three joint-row weights `(0,0,1)`. Therefore the bound applies to every legal table at C; it does not merely exclude one table common to three points.

Keep the ordered nonternary coordinates

    Q=(5,7,11,13,17,19,23),
    C_q=(q-1)/(q-2),  c_q=C_q/q.

At 5 the first-digit colours are `{0}`, `{1}`, `{2,3,4}`. At every other q they are `{0}`, `{1,...,q-1}`. Point C has local probabilities

    pi_C,5=(4/15,4/15,7/15),
    pi_C,q=(c_q,1-c_q), q != 5.                           (UF1)

The five ternary leaves are `(4,7,2,5,8) mod9`. Allow every normalized weight vector `w_l>=0`, `sum_l w_l=1`, and every retained table `0<=u_l(s)<=w_l` on the 192 full colour patterns, subject to the same Report810 K8 pointwise-null constraints for the 23 actual selected mixed originals. Those constraints use the literal phases in section 2 and are unchanged between C and the finite source below. Weights and tables are not fixed before the finite source is chosen.

Let `M(pi,u)` be the retained mass and `F_(D,S,h)(pi,u)` the Report820 CC4 common-colour envelope: `D` is the queried nonternary support, `S subset D` the coordinates queried at depth one, and `h=0,1,2` the ternary depth type. Define the same comparison numerator as Report820 CC8 at h16:

    G(pi,w,u)=12 L_cap(pi,u)-H16(w)
                         -27 T29 T1600 K_cap(pi,u),
    T29=120361/74088,
    T1600=4301685063112470380207/10^30.                  (UF2)

The hinge `H16` is the full-source hinge; the moment is calculated under the retained measure. Normalization remains

    alpha=nu_u(U),  mu=nu_u restricted to U / alpha

whenever `alpha>0`, with U the same actual old survivor. Positivity of the sufficient numerator would imply a positive certified denominator. A negative numerator does not bound the actual surviving mass above.

The complete head inventories, including fees for labels absent from this finite fixture, remain the inherited ones. The pure-29 factor occurs once and the complete Report804 continuation strictly above 1600 is unchanged. This tests the fixed complete continuation interface, not an inventory sharpened specifically to 53 originals.

The exact Report824 bound is

    G(pi_C,w,u) <= U_C=-0.18656447571285295... < -9/50   (UF3)

for every legal `w,u` just specified. The exact fraction, including the rational box-residual correction, is consumed from Report824's verified result. No optimizer is rerun here.

## 2. One actual finite family

The two anchors and all 23 actual mixed originals are the following `(modulus,residue)` pairs:

    (3,0), (9,1), (15,10), (21,7), (45,31),
    (33,22), (35,0), (39,13), (63,49), (51,34),
    (57,19), (55,0), (105,70), (75,25), (69,46),
    (65,0), (99,22), (77,0), (85,0), (117,13),
    (95,0), (165,55), (91,0), (147,49), (225,175).

At 5 add exactly these four pure originals:

    2 mod5;
    3+5^(j-1) mod5^j, j=2,3,4.                         (UF4)

At each `q in {7,11,13,17,19,23}` add exactly

    1 modq;
    2+q^(j-1) modq^j, j=2,3,4.                         (UF5)

For each q the four cylinders are disjoint. The first removes a different first digit from the three deeper cylinders; among the deeper cylinders, the first nonzero suffix digit occurs at a different position. Pure powers at different primes are numerically distinct, and none coincides with an anchor or mixed label. Thus the 28 pure originals and 25 displayed originals form one actual 53-original family with global numerical distinctness.

The normalized Haar survivor of a local pure family has mass and protected-root probability

    S_q=(q-2+q^-4)/(q-1),
    a_q=1/(q S_q)=(q-1)/[q(q-2+q^-4)].                 (UF6)

These are the finite-comb laws of Reports812 FS24–FS25 and 816, at the single prescribed depth E=4. Hence the actual colour law is

    pi_4,5=(a_5,a_5,1-2a_5),
    pi_4,q=(a_q,1-a_q), q != 5.                        (UF7)

No local marginal is selected from a different actual family. The seven laws are the CRT components of these same pure originals, with their ordinary Haar suffixes above depth four. The admissible ternary weights vary within this one family and source construction.

The integer 4 avoids every displayed mixed original and every pure original in UF4–UF5. The replay checks all 53 congruences directly. This finite witness is not asserted to survive arbitrary later originals.

## 3. Capacity factors remain on the same live menus

Write

    gamma_q=1-a_q/c_q=1/[q^4(q-2)+1],
    delta_5=TV(pi_4,5,pi_C,5)=2 c_5 gamma_5,
    delta_q=TV(pi_4,q,pi_C,q)=c_q gamma_q, q != 5.      (UF8)

Every protected singleton has `0<a_q<c_q`; every other category is above `c_q`. Every category at both endpoints is strictly above the second-depth cap `C_q/q^2`. The replay verifies these strict inequalities as rational comparisons for each prime. Consequently all colours remain live, and every query at depth at least two has the same generic capacity factor at both endpoints. The full three-type interface of Report820 applies without changing any maximizing menu.

Only the shallow clipping ratios can change:

    rho_q(c)=min(c_q,pi_q(c))/c_q.

They are all one at C. At the finite source a protected singleton has ratio `1-gamma_q`, and the other category retains ratio one. In particular

    0<rho_4,q(c)<=1,
    max_c |rho_4,q(c)-rho_C,q(c)|=gamma_q.             (UF9)

This is the extra sensitivity required beyond the unqueried-coordinate transport in Report812 FS21. A fixed-table continuity statement alone, such as the diagnostic passage in Report816, would not select one finite depth that works simultaneously against every table.

## 4. A uniform bound before choosing the kernel

Fix any legal `w,u`, but place no table-dependent constant in the estimates. For any common queried-colour tuple and permitted leaf subset, a branch average over coordinates outside D has an integrand in `[0,1]` because

    0 <= sum_(l in subset) u_l(s) <= sum_l w_l=1.

Telescoping through independent categorical coordinates gives the finite total-variation expectation bound

    |A_4-A_C| <= sum_(q outside D) delta_q.

The shallow factor of this same branch is the product of ratios for `q in S`. By UF9,

    |1-product_(q in S) rho_4,q(kappa_q)|
        <= sum_(q in S) gamma_q.

Multiplying an average in `[0,1]` by a factor in `[0,1]` therefore gives

    |branch_4-branch_C|
      <= sum_(q outside D) delta_q + sum_(q in S) gamma_q
      <= b_D,
    b_D=sum_(q outside D) delta_q+sum_(q in D) gamma_q. (UF10)

Both sides use the same common-colour tuple and the same actual table; no independent optimizing source or colour is introduced. Maxima over an identical finite menu preserve this uniform bound, so

    |F_(D,S,h)(pi_4,u)-F_(D,S,h)(pi_C,u)| <= b_D,
    |M(pi_4,u)-M(pi_C,u)| <= sum_q delta_q.            (UF11)

UF10–UF11 hold simultaneously for every admissible weight vector and retained table. This is the same uniform-selector mechanism used in [Report652](../650-699/652-a-realizable-obstruction-to-the-fixed-fifteen-star-criterion.md), section 6, and the total-variation/maxima argument of [Report812](812-fractional-categorical-kernels-admit-explicit-finite-pure-families.md), FS21, with the shallow-capacity term included.

## 5. Complete inventories and exact error

There are `3^7` nonternary depth types and three ternary types, thus 6,561 full `(D,S,h)` terms. Use the complete coefficients `B_(D,S)`, `W_(D,S)` and nonnegative residual head coefficients from [Report820](820-queried-colour-capacities-sharpen-complete-head-and-moment-bounds.md), CC5–CC7. Every selected label is subtracted only from its own complete numerical depth type. Include the `B_(D,S)/2` higher-ternary debit at h=2, including D empty.

Write the complete nonnegative coefficient multiplying each envelope in the negative part of UF2 as

    A_(D,S,h)=12 loss_(D,S,h)
                 +27 T29 T1600 W_(D,S) t_h,
    (t_0,t_1,t_2)=(1,15,216).

The hinge depends on w and is unchanged when pi changes. Applying UF11 term by term, with coefficient signs preserved, gives

    G(pi_4,w,u) <= G(pi_C,w,u)+Delta_4,
    Delta_4=12 sum_q delta_q
                     +sum_(D,S,h) A_(D,S,h) b_D.       (UF12)

The error bound b_D does not depend on S. Therefore its coefficient sum can be aggregated into 384 `(D,h)` blocks. This does not assert that the finite-source gate itself has only 384 depth types: its shallow responses generally depend on S.

For checking that aggregation, define

    beta_D=product_(q in D) 1/(q-2),
    W_D=product_(q in D) C_q A4(q),
    A4(q)=15t+50t^2+60t^3+24t^4, t=1/(q-1).

The sum of B over S is beta_D and the sum of W is W_D. The aggregated shallow head coefficient is beta_D on `h=0, |D|>=2` or `h=1,2, D nonempty`, and zero otherwise; subtract the selected coefficients `C_D/n` in their correct blocks. Add beta_D/2 for h=2. This yields exactly the 384 C-point coefficients used by Report824. The consumer reconstructs all 6,561 types, checks their residual nonnegativity and verifies every aggregation identity.

The exact value is

    Delta_4=
      28865551539509647988542784319586370884912994471882288221506582506964216584496397811
      /1890266140845948552511928762620577495044158529536000000000000000000000000000000000000
      =0.015270628254808332... < 1/50.                  (UF13)

Its mass contribution is `0.0035962566080624822...`; its envelope-debit contribution is `0.01167437164674585...`. All calculations are rational; decimals are display values only.

Combining UF3 and UF12–UF13 gives, uniformly over every legal `w,u`,

    G(pi_4,w,u) <= U_C+Delta_4
                 =-0.1712938474580446... < -4/25.     (UF14)

The strict rational conclusion also follows immediately from `U_C<-9/50` and `Delta_4<1/50`. It does not claim that UF14 is the optimal uniform bound.

The quantifier order is one fixed actual family, then every admissible table and leaf-weight choice. Thus allowing source-adaptive choices within this same first-colour table class does not evade UF14. A depth chosen separately after fixing each table would have been a weaker result and is not used here.

## 6. Reproduction and remaining scope

The [consumer](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/finite_source_uniform_kernel_obstruction.py), [certificate](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/finite_source_uniform_kernel_obstruction_certificate.json), and [result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/finite_source_uniform_kernel_obstruction.json) use only the Python standard library and explicit input files. Run beside the Report824 dual certificate and result:

```sh
python3 -I -S -B finite_source_uniform_kernel_obstruction.py
```

Ordinary execution compares the reconstruction to the saved result without modifying it. `--write-result` explicitly regenerates this report's result. Alternate paths are available for both report-specific inputs and the two upstream files. No package import, solver, directory traversal, depth search or source-domain sweep is performed.

The consumer checks the Report824 certificate/result hashes, phase and semantic-model identity, C-only support and exact rational upper bound. It consumes that established dual theorem; it does not independently rerun its proof. Its 9,399 explicit checks cover the finite combs, joint original inventory, clipping branches and deep-cap inequalities, all depth types and aggregated coefficients, rational error budget and strict negative conclusion. Normal, optimized and relocated optimized execution reproduce the same result; 14 semantic or saved-result mutation classes are rejected under optimized execution. Separate independent reconstruction performed 7,011 checks, including direct enumeration on each local `q^4` carrier and reconstruction from all full depth types. These are distinct checks, not an added Lean claim.

The obstruction concerns the specified inherited complete comparison at h16. It does not exclude sharper actual-family cylinder caps or inventories, a different threshold or hinge, stronger moment/continuation bounds, retained states that observe deeper source digits, or a different valid noncoverage argument. It supplies neither an upper bound on actual survival nor any covering example or unrestricted impossibility theorem. Its reusable result is that this exact comparison failure already occurs for one finite actual family, uniformly over its full admitted kernel class, rather than only at a limiting categorical point.
