# Coherent prefix moments preserve the complete height remainder

A finite-prefix moment bound can replace part of the supportwise maximum-depth bound while preserving all heights and one common retained source. The additional finite data must keep one globally consistent phase at each numerical query label. A complete finite example on divisors of 45 gives a strict gap between summing separately optimized tuple masses and optimizing one complete phase layout. This is an ordinary mathematical bridge, not a positive certificate for the seven-prime problem or a Lean result. It sharpens the retained-source interface of [Report815](815-retained-source-moments-have-a-three-point-common-kernel-obstruction.md) by enforcing one phase per numerical label throughout the finite fourth-moment expansion.

## 1. One genuine retained source and a complete finite prefix

Keep the actual product source lambda_w, the genuine categorical submeasure nu_u<=lambda_w, the complete actual old survivor U, and the selected-null conditions of the retained-source moment bridge. The source used in the eventual continuation is mu_u=nu_u|U/alpha_u, alpha_u=nu_u(U)>0.

Choose a finite ternary query depth J>=2 and finite nonternary query depths E_q>=1. Put

    N_E=3^J product_q q^E_q,
    D_E={n:n divides N_E}.

The prefix query includes EVERY numerical divisor in D_E, including its unit term. A layout is one assignment

    a_n in Z/nZ for every n in D_E, with a_1=0.

It defines

    Q_(E,a)(x)=sum_(n inD_E) 1_{x=a_n modn}.

The phases are otherwise independent across distinct numerical labels; no nesting assumption is imposed. Within one layout, however, each numerical label has only one phase, shared in every occurrence when the fourth power is expanded.

Suppose a verified bound B_E satisfies

    B_E >= max_a integral Q_(E,a)^4 dnu_u.                      (P1)

This bound is for the same unnormalized nu_u. It is not a moment of a separately normalized colour cell or a different pure-source law.

For any four possibly different prefix layouts, Holder's inequality gives

    integral product_(i=1)^4 Q_(E,a_i) dnu_u
       <= product_i (integral Q_(E,a_i)^4 dnu_u)^(1/4)
       <= B_E.                                                (P2)

Holder holds for every finite positive measure; nu_u need not have mass one. Its unit-query fourth moment is nu_u(whole), not 1. Conversely, choosing all four layouts equal shows that the supremum of the mixed four-query integral is exactly the maximum in P1. Thus P1 retains the entire mixed-query requirement while reducing its exact finite definition to one global phase table.

## 2. Separate the finite prefix from the unbounded maximum-depth expansion

Let F_D0,F_D1,F_D2 be the same common-colour envelopes from the retained-source bridge. Define

    A4,E(q)=sum_(e=1)^E [(e+1)^4-e^4]/q^e,
    W_D,E=product_(q inD) C_q A4,E_q(q),
    c_J=sum_(j=2)^J [(j+1)^4-j^4] 3^(2-j).

The empty product is 1. At J=2, c_J=65; as J grows, c_J increases to 216. Write

    K_E=sum_D W_D,E (F_D0+15F_D1+c_J F_D2),                    (P3)
    K_infinity=sum_D W_D,infinity (F_D0+15F_D1+216F_D2),
    W_D,infinity=product_(q inD) C_q A4(q).

K_E is precisely the old termwise upper-bound sum over ordered quadruples whose four numerical labels all lie in D_E. The tuple is inside the prefix exactly when its maximum exponent at every coordinate lies below the declared cutoff. K_infinity sums the corresponding nonnegative bounds over all finite depths.

Consequently

    R_E=K_infinity-K_E>=0                                    (P4)

is the complete bound for the remaining ordered tuples, including all cross terms in which only some of the four labels leave the prefix. It is not a bound obtained by discarding all high labels before taking a fourth power. Every active coordinate still receives one cylinder cap C_q, and every high ternary depth retains its Haar factor.

For four arbitrary complete finite-head queries, split their ordered-tuple expansion into the prefix quadruples and its complement. Apply P2 to the prefix part and the original maximum-depth cylinder bound to the complement. If the actual head is smaller than the chosen prefix, it can be enlarged by adding nonnegative query terms; the dominating cylinder model extends to the needed finite depths. This proves

    integral Q1 Q2 Q3 Q4 dnu_u <= B_E+R_E.                    (P5)

One may replace B_E by min(B_E,K_E), because both are independently valid prefix bounds. Thus the nonnegative improvement over the old moment bound is

    K_E-min(B_E,K_E).

All heights remain charged. No global phase identity is imposed outside the finite prefix, so P5 is a conservative interface even when the high query layouts are unknown.

Restriction to U only decreases the nonnegative integrals. Hence the normalized retained-source mixed moment is at most (B_E+R_E)/alpha_u. The full-source hinge remains valid by domination, the actual pure29 factor T29 still occurs once, and for 0 <= h < 28 the unchanged source-independent tail allowance T yields the sufficient numerator

    (28-h)L(pi,u)-H_h(w)-27T29 T [B_E+R_E].                   (P6)

No mass from another source or separately optimized denominator appears here.

## 3. The additional boundary data are substantive

The original coarse first-colour vector pi generally does not determine the actual prefix distribution needed in P1. For example, equality of two first-digit marginals does not determine a cylinder at q^2. The new data can be given as the actual normalized local prefix laws

    xi_q(a)=lambda_q(a modq^E_q),

with their common-source provenance and exact projection onto the original colour probabilities. The ternary prefix law uses the same five weights and Haar suffix. Because the retained table sees only first colours, these actual prefix laws determine the unnormalized finite-carrier measure in P1 exactly.

All-height cylinder caps remain separate premises supplied by the actual pure-family construction. Valid prefix probabilities or finitely many prefix cylinder inequalities do not themselves establish every higher-height cap. The remainder P4 must continue to use verified all-height constants.

An even stronger conditional version can use

    Gamma_E(c)=nu_u(U intersect prefix_cell(c))

and a bound B_E^U on the global-layout fourth moment under that one unnormalized joint prefix profile. Then

    integral Q1 Q2 Q3 Q4 d(nu_u|U) <= B_E^U+R_E

still holds, since the outside-prefix tuples are safely bounded under nu_u. Gamma_E carries actual survivor correlations between coordinates. It cannot be reconstructed from unrelated local marginals or from the source lower bound L alone. Its mass sum is the actual alpha_u; if only partial bounds on Gamma_E are known, their consistency and relation to the same alpha_u must be certified. One must not subtract an upper bound on deleted mass from a moment upper bound as if it were a lower bound on the removed moment.

This interface therefore makes the missing information explicit: actual prefix cylinder masses and one consistent phase table, or the stronger actual joint survivor-prefix masses. It does not make these records free to obtain.

## 4. Finite convex/linear certification is retained with the right parameters

Fix 0 <= h < 28. For the raw-source version P1, take B_E to be the exact finite maximum in P1, and take each entire xi_q vector as one local probability block. At a fixed layout a, the integral in P1 is affine in that block with all other blocks fixed; the table u and full source stay fixed. The maximum over the finite layout set is therefore convex in each whole local block.

R_E is also block-convex. Its coefficients on F_D0,F_D1,F_D2 are respectively

    W_D,infinity-W_D,E,
    15(W_D,infinity-W_D,E),
    216W_D,infinity-c_J W_D,E,

all nonnegative. The original source mass is affine and its deletion envelopes are convex, so L remains block-concave after projecting xi onto the coarse colour vectors. Thus P6, with this exact B_E, is block-concave in the whole local prefix blocks. A separately convex certified upper bound for B_E also suffices. An arbitrary valid upper bound need not have this property. Likewise, the optional pointwise replacement by min(B_E,K_E) is always a valid moment bound, but its block-convexity is not automatic; the block-concavity argument here uses the exact B_E without that replacement.

At a fixed prefix-law vertex, every complete-layout integral in P1 is linear in the shared retained coefficients u. An epigraph variable with one inequality for every complete prefix phase layout, together with the usual common-colour residual epigraphs, gives a finite linear sufficient certificate. The same u,w must be used throughout each certified product domain. The phase-layout inequalities are not replaced by independently maximized tuple inequalities, since that would undo the improvement.

The stronger conditional Gamma_E version has this LP structure only when its relation to the common source and u is supplied by a valid fixed linear/multiaffine representation, for example a sufficiently detailed actual finite carrier with fixed U. Treating arbitrary Gamma_E entries as independently choosable probabilities is not an admissible relaxation of a common source.

Finite does not imply small. Even J=2 and E_q=1 for the seven old nonternary primes gives 384 numerical query labels. Direct enumeration of all phase tables is not proposed. An efficient implementation would need exact upper certificates exploiting the finite phase-consistency structure; positivity or tractability of such certificates is not established here.

## 5. A strict finite gap on the same five-leaf source

Take Q={5}, weights w_l=1/5 on leaves (4,7,2,5,8), and Haar at5. The full product source is uniform on its 25 live residues modulo45, each of mass1/25. Choose one dominated retained measure with nonzero masses only at

| Residue mod45 | Retained mass |
| ---: | ---: |
| 2 | 1/25 |
| 4 | 3/100 |
| 7 | 3/200 |
| 13 | 3/200 |

Its total mass is 1/10. This is realized by one first-digit retained table u<=w: multiply each displayed mass by5 to obtain its leaf/5-digit coefficient; all other entries are zero. It uses the actual same product source throughout.

Let the prefix labels be ALL divisors of45:

    1,3,5,9,15,45.

There are exactly3 times5 times9 times15 times45=91,125 complete independent phase tables. Exhaustive integer arithmetic gives

    max_a integral Q_(E,a)^4 dnu_u = 417/8.

A maximizing layout assigns phase2 at each of the five nonunit numerical labels. This is an actual complete phase table; arbitrary nonnested tables are included in the enumeration.

The literal cylinder maxima are

    d=1: 1/10,   d=3: 3/50,   d=5: 11/200,
    d=9: 9/200,  d=15: 1/25,  d=45: 1/25.

Independently maximizing every compatible ordered tuple and summing gives

    sum_(n1,...,n4) max_phases nu_u(intersection) = 211/4.

The strict difference is

    211/4-417/8=5/8>0.

Here the termwise cylinder bounds are exact maxima, not loose inherited cap estimates. The discrepancy comes from phase consistency: the largest mod3 and mod9 cylinders prefer the first ternary root/leaf, while the mixed and deepest tuples prefer residue2. A globally fixed numerical query phase cannot achieve all of these maxima together.

For the same source with Haar suffixes and the valid sharp constant C5=1, the full-height generic moment is

    K_infinity=2420243/6400,

and the finite-box generic bound is exactly K_E=211/4. Keeping the entire remainder while replacing only the coherent finite prefix gives

    B_E+(K_infinity-K_E)=2416243/6400.

The strict gain remains exactly5/8; it is not obtained by dropping high terms. This example establishes a real difference between the two moment interfaces. It does not instantiate the full selected23-label family of Report815, and its gain is not claimed sufficient for the seven-prime continuation problem.

## 6. Exact reproduction

The [standalone program](../../../frontier/cover-geometry/coherent-query-moments/retained_prefix_phase_coherence.py) and [generated result](../../../frontier/cover-geometry/coherent-query-moments/retained_prefix_phase_coherence.json) reproduce the finite example.

```sh
python3 -I -S -B retained_prefix_phase_coherence.py
```

Normal execution reconstructs the exact result and checks the saved file without rewriting it. Use `--write-result` only to regenerate the file. The program checks all 91,125 phase tables, the one dominated source, exact ordered-tuple counts, the literal cylinder maxima, and the all-height remainder identity in 91,211 explicit checks. Integer and rational arithmetic carry all comparisons. No solver or source-grid scan is used. Holder supplies the mixed-query conclusion; no enumeration of 91,125^4 layout quadruples is claimed. The program uses explicit checks that remain active under Python optimization.
