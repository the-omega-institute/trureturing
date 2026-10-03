# Fractional categorical kernels admit explicit finite pure families

One fixed fractional retained table and one fixed five-leaf source law pass the complete 29-admission and prime-tail certificate for explicit finite pure-prime families. Each old nonternary prime may have its own finite depth E_q >= 3. Under the selected 23-label phase conditions stated below, all remaining permitted old phases are arbitrary, and the final distorted survivor mass is strictly greater than 13/1000 after arbitrary 29 originals and every finite prime tail strictly above 1600.

The same table has a positive certificate at the all-upper categorical probability point, with source lower bound approximately 0.0336694793511 and continuation numerator approximately 0.0388351796518. It fails the full 320-vertex categorical relaxation: one vertex has source lower bound approximately -0.0194053261432. The finite-pure theorem follows from an explicit total-variation transport estimate around the positive point. It does not assert success on every categorical source vector or every actual phase family.

These are ordinary mathematical arguments and exact rational checks. No Lean result, LP optimality, arbitrary-phase old-source theorem, or solution of unrestricted Erdős #7 is asserted.

## 1. The actual family and common-source contract

Use

    Q=(5,7,11,13,17,19,23),
    ternary leaves (4,7,2,5,8) mod9,
    roots A={4,7}, B={2,5,8}.

The full actual family is finite and has pairwise numerically distinct odd moduli greater than one. Its prime support is contained in

    {3,5,7,11,13,17,19,23,29} union {primes strictly greater than1600}.

There are no other prime directions between 29 and the tail cutoff. If pure originals of modulus 3 or 9 are present, their phases are respectively 0 and 1. Pure ternary originals of every height at least 3 may have arbitrary phases and remain charged by the complete inventory.

At each q in Q choose a finite integer E_q >= 3. The actual pure-q originals are exactly the following family, with no arbitrary additional pure-q deletions. At q=5 they are

\[
2\bmod5,\qquad (3+5^{j-1})\bmod5^j\quad(2\le j\le E_5).
\tag{FS1}
\]

At q in Q other than 5 they are

\[
1\bmod q,\qquad (2+q^{j-1})\bmod q^j\quad(2\le j\le E_q).
\tag{FS2}
\]

The selected shallow mixed numerical slots and their sufficient actual phases are

| Modulus | Phase | Modulus | Phase | Modulus | Phase |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 15 | 10 | 21 | 7 | 45 | 11 |
| 33 | 22 | 35 | 0 | 39 | 13 |
| 63 | 49 | 51 | 34 | 57 | 19 |
| 55 | 0 | 105 | 70 | 75 | 25 |
| 69 | 46 | 65 | 0 | 99 | 22 |
| 77 | 0 | 85 | 0 | 117 | 13 |
| 95 | 0 | 165 | 55 | 91 | 0 |
| 147 | 49 | 225 | 175 | | |

Every selected slot that is present must satisfy the pointwise retained-null condition below; the displayed phases are the concrete sufficient contract checked by the certificate. An absent selected slot has no phase requirement. Subtracting its numerical contribution from the complete residual inventory remains valid because it removes no remaining actual original. The theorem does not allow a present selected slot to change phase without rechecking the same null condition.

All other old mixed originals supported on {3} union Q may have arbitrary actual phases and arbitrary finite exponents. All originals whose largest prime is 29, and all originals in the declared later-prime support, are handled by the complete continuation. Modulus distinctness is global across these parts.

The five weights, in leaf order, are

\[
w=\frac1{10^6}(236809,236809,226024,150179,150179).
\tag{FS3}
\]

Thus

\[
r=\max(w_0+w_1,w_2+w_3+w_4)=\frac{263191}{500000},\qquad
v=\max_lw_l=\frac{236809}{10^6}.
\tag{FS4}
\]

For each q let lambda_q be the normalized Haar survivor of its actual pure family (FS1) or (FS2), with the Haar suffix retained above the finite depth. Together with the five-leaf ternary law and its Haar suffix, these give one full source

\[
\lambda_w=\lambda_{3,w}\otimes\bigotimes_{q\in Q}\lambda_q.
\tag{FS5}
\]

No separate law is chosen for a selected original, a query or a later prime.

## 2. A fixed fractional retained table

The first-digit partition at 5 is {0},{1},{2,3,4}; at each other q it is {0},{1,...,q-1}. There are 3 times 2^6 = 192 full colour patterns and five leaf indices. Use the fixed table u_l(s) in the [certificate](../../../frontier/cover-geometry/refined-capped-source/categorical_kernel_stability_certificate.json). Pattern indices are lexicographic in these seven ordered colour alphabets.

Every entry satisfies

\[
0\le u_l(s)\le w_l.
\tag{FS6}
\]

There are 960 entries: 134 are positive, of which 106 equal their full leaf weight and 28 are strictly fractional. For example u_2(156)=8179/10^6 is positive and smaller than w_2=226024/10^6. The union of the selected-null restrictions forces 750 entries to zero; additional zeros are retained by the fixed candidate.

For a selected actual cylinder with ternary-compatible leaf l and queried colour assignment kappa, the table satisfies

\[
u_l(\kappa,s_{Q\setminus D})=0
\quad\text{for every outside colour completion}.
\tag{FS7}
\]

This is a condition on the one actual phase and the same table. It is checked on every compatible leaf. It is independent of the numerical probability values at the unqueried coordinates, so it remains valid along all finite pure families (FS1)–(FS2).

Replacing the coefficient w_l by u_l(s), without any cellwise division or normalization, defines a genuine submeasure nu_u <= lambda_w. The categorical retained-kernel interface of [Report810](810-categorical-retained-kernels-give-a-finite-common-source-interface.md) applies even though the table need not be a decreasing Boolean core. This changes a hypothesis of [Report809](809-two-colour-core-obstructs-every-fixed-weight-full-box-certificate.md)'s fixed-core obstruction; it does not contradict that obstruction.

## 3. The complete source lower bound and continuation

Write C_q=(q-1)/(q-2). These satisfy 1 <= C_q <= q and the actual all-height cylinder bounds lambda_q(a mod q^e) <= C_q/q^e. Let pi_q be the categorical probability vector induced by the one actual lambda_q. For a queried support D and one common colour assignment kappa, put

\[
A_{l,D,\kappa}(\pi,u)
=\sum_{s_{Q\setminus D}}\prod_{q\notin D}\pi_{q,s_q}\,
 u_l(\kappa,s_{Q\setminus D}).
\tag{FS8}
\]

The envelopes are

\[
F_{D,0}=\max_\kappa\sum_l A_{l,D,\kappa},\qquad
F_{D,1}=\max_{R,\kappa}\sum_{l\in R}A_{l,D,\kappa},\qquad
F_{D,2}=\max_{l,\kappa}A_{l,D,\kappa}.
\tag{FS9}
\]

Each sum uses one common kappa. The maxima bound the loss of an arbitrary actual cylinder; they do not choose new source phases. The retained initial mass is M=F_empty,0, evaluated at the actual probability vector.

Let beta_D=product_(q in D)1/(q-2), with beta_empty=1. For each shallow inventory type subtract each selected numerical slot once:

\[
R_{D,h}=\beta_D-
\sum_{\substack{3^hn\text{ selected}\\\operatorname{supp}(n)=D}}
\frac{C_D}{n}.
\tag{FS10}
\]

Use (FS10) for h=0 with |D|>=2 and for h=1,2 with D nonempty, and set the other shallow coefficients to zero. All coefficients are nonnegative. The complete lower bound is

\[
L(\pi,u)=M-
\sum_D\bigl(R_{D,0}F_{D,0}+R_{D,1}F_{D,1}+R_{D,2}F_{D,2}\bigr)
-\frac12\sum_D\beta_DF_{D,2}.
\tag{FS11}
\]

The last sum includes D=empty and all higher ternary heights, since sum_(h>=3)3^(2-h)=1/2. Arbitrary finite cofactor exponents are included in beta_D. If U denotes the full actual old survivor, then

\[
\lambda_w(U)\ge\nu_u(U)\ge L(\pi,u).
\tag{FS12}
\]

A positive lower bound alpha is used to normalize only the full source restriction

\[
\mu=\lambda_w|_U/\lambda_w(U).
\tag{FS13}
\]

The retained table certifies the denominator. It is not normalized separately to provide the query or fourth-moment law.

At h=16 use the full-source hinge H=H_0+H_r r+H_v v from Report810, and the full fourth-moment numerator

\[
K=\prod_{q\in Q}[1+C_qA_4(q)]\,[1+(28/27)A_4(29)]\,
 (1+15r+216v),
\quad
A_4(q)=\frac{15}{q-1}+\frac{50}{(q-1)^2}
 +\frac{60}{(q-1)^3}+\frac{24}{(q-1)^4}.
\tag{FS14}
\]

The full-source mean is included in H; only its subthreshold correction is a finite sum. The same source-independent full-tail allowance as [Report804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md) is

\[
T_{1600}=\frac{4301685063112470380207}{10^{30}}.
\tag{FS15}
\]

The consumer regenerates all 179 primes from 1601 to 2999, applies the upward-rounded complete quartic bridge, and includes the analytic tail above 3000. Thus (FS15) is not a truncation at 3000. Under the support and phase conditions in section 1, a positive

\[
\varepsilon=12\alpha-H-27KT_{1600}
\tag{FS16}
\]

gives final distorted survivor mass at least epsilon/(27 alpha), by the common-source 29 and tail continuation. The inherited constants, pure-29 conditioning and exact prime support are part of this statement.

## 4. A positive point and a failed uniform relaxation

The all-upper categorical point is

\[
\pi^\star_5=(4/15,4/15,7/15),\qquad
\pi^\star_q=(c_q,1-c_q),\quad
c_q=\frac{q-1}{q(q-2)}\quad(q\ne5).
\tag{FS17}
\]

The one fixed table gives

\[
\alpha_\star=L(\pi^\star,u)
=\frac{414806475971835287}{12319955163140625000}
=0.03366947935109953\ldots,
\tag{FS18}
\]

and epsilon_star=0.038835179651844895... > 0. Its evaluated point reserve is 0.04271940091816107.... Exact fractions for the numerator, hinge and moment are retained in the [result](../../../frontier/cover-geometry/refined-capped-source/categorical_kernel_stability.json). A point of the categorical relaxation need not be attained by a finite pure family, so these values alone are not the finite-source theorem.

The 5-coordinate capped simplex has five vertices; each of the other six binary simplexes has two. All 320 product vertices were evaluated using exactly the same weights and retained table. The smallest source value is attained at

    pi5=(0,1/5,4/5),
    pi7=pi11=pi13=pi17=pi19=(0,1),
    pi23=(22/483,461/483).

Its source lower bound is

\[
-\frac{14318795602769663}{737879667525000000}
=-0.019405326143214986\ldots.
\tag{FS19}
\]

This is a countercontrol to full-relaxation success of this fixed candidate. It neither proves actual coverage nor excludes a different table or a source domain restricted by actual pure-family data. The construction below uses such data explicitly.

## 5. Total-variation stability for a fixed retained table

Fix any legal w,u and complete residual coefficients as in Report810. For two categorical vectors pi and pi', write delta_q=TV(pi_q,pi'_q). Define

\[
\ell_q=1+
\sum_{D:\,q\notin D}
\left[R_{D,0}+rR_{D,1}+v\left(R_{D,2}+\frac12\beta_D\right)\right].
\tag{FS20}
\]

Then

\[
|L(\pi,u)-L(\pi',u)|\le\sum_{q\in Q}\ell_q\delta_q.
\tag{FS21}
\]

For a change at one coordinate q, the integrand defining M lies in [0,1], because sum_l u_l(s)<=sum_l w_l=1. The expectation changes by at most delta_q. If q belongs to the queried support D, the envelope does not use pi_q. Otherwise each no-ternary branch lies in [0,1], each root branch in [0,r] and each leaf branch in [0,v]. The finite total-variation expectation inequality gives the respective constants 1,r,v. A maximum of functions with a common Lipschitz constant has that constant. Multiplying by the nonnegative complete inventory coefficients proves the one-coordinate bound, and telescoping through the coordinates proves (FS21).

Every intermediate probability vector is a valid product categorical vector; it need not be an actual finite pure survivor. The proof uses neither joint concavity nor monotonicity of L with respect to a pure-family depth.

The full-source H and K depend on w and the inherited cylinder caps, not on pi. Therefore a common debit

\[
D_{\rm TV}\ge\sum_q\ell_q\delta_q
\tag{FS22}
\]

gives

\[
\alpha\ge\alpha_\star-D_{\rm TV},\qquad
\varepsilon\ge\varepsilon_\star-12D_{\rm TV}.
\tag{FS23}
\]

This estimates the same source certificate and continuation. It does not independently optimize the table at either endpoint.

## 6. Actual finite pure families with separately varying depths

The cylinders (FS1) are pairwise disjoint: the height-1 deletion has first digit 2; every deeper deletion has first digit 3; for heights i<j the larger-height phase reduces to 3 modulo 5^i, while the height-i phase is 3+5^(i-1). The same argument for (FS2) uses first digits 1 and 2. The referenced digits 0 and 1 at 5, and 0 at the other primes, are untouched.

The surviving Haar mass at q is 1-sum_(j=1)^E_q q^(-j), so the probability of each protected digit is

\[
a_q(E_q)
=\frac{1/q}{1-\sum_{j=1}^{E_q}q^{-j}}
=\frac{q-1}{q(q-2+q^{-E_q})}.
\tag{FS24}
\]

The conditional law has all-height cylinder density at most the reciprocal of this survivor mass, which is less than or equal to C_q. Thus the same inherited caps used in (FS11), H and K apply. At 5 the categorical law is (a_5,a_5,1-2a_5); elsewhere it is (a_q,1-a_q).

Consequently the exact categorical distances from (FS17) are

\[
\delta_5(E_5)=2(c_5-a_5(E_5)),\qquad
\delta_q(E_q)=c_q-a_q(E_q)\quad(q\ne5).
\tag{FS25}
\]

Each a_q(E_q) increases to c_q, so every distance in (FS25) is bounded by its value at depth 3 whenever E_q>=3. The depths may vary independently; no assertion that L itself increases with depth is needed.

In prime order, the depth-3 distances are

\[
\left(\frac1{705},\frac1{10010},\frac1{118602},
\frac1{288002},\frac1{1174530},\frac1{2092394},\frac1{5609562}\right).
\tag{FS26}
\]

Using the exact coefficients (FS20) gives the common debit

\[
D_{\rm TV}
=\frac{154096315250710193625636768436889}
       {66955378149672504286220278602750000}
=0.002301477782803978\ldots.
\tag{FS27}
\]

For every independently chosen finite E_q>=3 this gives

\[
\alpha_{\rm floor}
=\frac{262532050850593586762106198453983029}
       {8369422268709063035777534825343750000}
=0.03136800156829555\ldots,
\tag{FS28}
\]

and

\[
\varepsilon_{\rm floor}
=12\alpha_{\rm floor}-H-27KT_{1600}
=0.01121744625819716\ldots>\frac1{100}.
\tag{FS29}
\]

The exact rational comparison is

\[
\frac{\varepsilon_{\rm floor}}{27\alpha_{\rm floor}}
=0.013244738324220753\ldots>\frac{13}{1000}.
\tag{FS30}
\]

Use alpha_floor itself as the certified denominator bound in (FS13)–(FS16). This proves the advertised finite-pure-family continuation under section 1's support and phase conditions. It is not necessary to infer monotonicity of a ratio by independently replacing its numerator and denominator.

At depth 3 the seven pure inventories together contain 21 distinct numerical labels, none equal to a selected mixed label or to 3 or 9. For arbitrary finite depths the same distinctness follows from unique prime factorization. The proof therefore uses actual compatible originals in one finite family. It does not combine separately attainable local optima into an undeclared joint source.

## 7. Exact controls and limitations

The standalone [consumer](../../../frontier/cover-geometry/refined-capped-source/categorical_kernel_stability.py) reads only the explicit certificate and result paths, defaulting to files beside itself. It has no solver dependency and performs no directory traversal. It reconstructs the complete residual inventory, all selected pointwise-null conditions, the 128 common-colour support menus, full h=16 hinge, complete 179-prime tail bridge, all 320 vertices, exact depth-3 pure laws and the transport debit.

The retained result contains no elapsed-time fields. There are 4,461 explicit checks, plus the final result replay. Normal and optimized execution and relocation to a path containing spaces pass. Eleven critical mutation classes are rejected in both modes: oversized retention, selected-null violation, unnormalized weights, wrong continuation normalization, duplicated or omitted entries in the fixed 23-slot certificate, an omitted tail-bridge prime, forged depth-3 and 320-vertex claims, a forged result and a duplicate JSON key. Omitting a slot from this fixed certificate while leaving its present actual original is distinguished from the theorem's permission for an actual selected original to be absent. Python assert is not used, so optimization does not disable verification.

Independent exact checks reproduced the point certificate, the negative vertex and the finite-pure transport. The separate point/nullity/menu check, countercontrol and stability verification together performed 28,630 checks. They verify the stated ordinary arithmetic and support the proofs above; none is a Lean result.

The quantitative theorem keeps the same table, weights, actual selected phase contract, pure-family construction and prime support. The 320-vertex failure remains part of the result. Additional arbitrary old pure deletions, unrestricted selected phases, other intermediate primes, a uniform positive optimizer over all families and unrestricted Erdős #7 remain outside this certificate.
