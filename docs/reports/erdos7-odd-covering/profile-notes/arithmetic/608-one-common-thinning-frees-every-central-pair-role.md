# One common thinning frees every central pair role

All central residues at the120 retained pair labels may now be arbitrary,
with one fixed thinning matrix valid for every globally chosen layout.
Under the fixed pure-source and star hypotheses of
[Report606](606-common-envelopes-free-all-square-pair-central-roles.md),
the complete ten-prime survivor has Haar mass greater than1/104000.

The proof covers all64^30=2^180 canonical padded assignments by reducing
to ten aligned profiles and certifying64 exhaustive branches. It preserves
Report606's actual pure3/pure5 source, central15 role, star roles, new9q/25q
roles, complete coefficient arrays and all permitted original/query heights.
The retained inventory stays156 labels. No additional numerical modulus is
admitted. This is ordinary mathematics with a standard-library exact
rational certificate, not new Lean verification.

## 1. Statement and quantifiers

Let V={7,11,13,17,19}, and retain the twelve pair labels

    3^a 5^b q^e r^f,
    (a,b) in {0,1}^2,
    (e,f) in {(1,1),(2,1),(1,2)},

for each of the ten pairs q<r in V. Every original may be absent or present once. Every present residue is fixed globally, and all central and outside components at these 120 labels may be arbitrary. All other hypotheses remain those of Report606. More explicitly, the permitted pure3/pure5 originals are a subset of

    2 mod3, 7 mod9, 4 mod27, 13 mod81, 40 mod243, 121 mod729;
    4 mod5, 2 mod25.

There are no other pure3/pure5 originals. Missing listed originals may be imposed as auxiliary deletions. The central15 component is0. Set j_7=1, j_11=2, and j_13=j_17=j_19=3. The central components of3q and3q^2 are0 mod3; those of5q and5q^2 are j_q mod5;15q has point(0,j_q). The9q component is1 mod9 and the25q component is12 mod25. All outside components remain arbitrary.

Other mixed originals on the first seven primes satisfy the inherited inventory condition: some exponent is at least3, or both central exponents are at most1, or at least five prime divisors occur. All originals touching23,29 or31 are unrestricted. Other pure powers remain unrestricted. These conditions do not free the pure or star phases, enlarge the retained inventory, or prove unrestricted odd noncoverage.

At one outside exponent type a present central row, column and point have 3*5*15=225 possible assignments. Source-null or missing roles can be padded once into the retained rectangle {0,1}x{0,1,2,3}, without changing any actual original. Padding only increases the activation cap. The canonical profile set A thus consists of the64 functions

    alpha_(R,C,I,J)(i,j)
      =1+1_(i=R)+1_(j=C)+1_((i,j)=(I,J)).          (SR1)

The padding is fixed per original family and independent of future queries.

The certificate fixes ONE theta in [0,1]^14, expanded to the same fourteen leaf blocks as Report606. It proves

    exists theta, for every actual family C,
      there exists C's actual conditional survivor submeasure nu_C
      whose complete continuation gate is at least gamma>0.   (SR2)

It does not claim one common probability law nu for all families. The same theta is used for mass and every query within each family's one actual source.

## 2. Reduction from 30 profiles to ten aligned profiles

Write kappa_e=p_e+s_e for the Report606 full pair cap weight. An actual family has

    beta_e=sum_(t=0,1,2) w_(e,t) alpha_(e,t),
    sum_t w_(e,t)=kappa_e,

with all three weights positive. The uniform strict region throughout 0<=beta_e<=4kappa_e has already been established: the minimum full matching polynomial at the upper corner is

    31820206188505/126963499999921>0,

and the largest disjoint-neighbor sum is 6053127/13633361<1. Therefore every mass/query grid is defined on this entire comparison domain, with no role-dependent change of mask.

For fixed theta, let

    K(theta,beta)=(1-c)M(theta,beta)
                    -sum_j tau_j max_k Q_(j,k)(theta,beta),
    tau_j=(1-c)L_j+cW_j>=0.                         (SR3)

Here j indexes the central query modes and outside support; k indexes its complete finite selector family. The unit term is already included through 1-c. The mass and each selected query are affine in the entire vector beta_e when other edges are held fixed: no matching term uses the same edge twice. Thus K is concave separately in beta_e.

Since beta_e/kappa_e is a convex combination of three members of A, Jensen gives

    K(theta,beta)>=min_(alpha in A)
       K(theta,beta with beta_e replaced by kappa_e alpha).

Apply this successively to the ten edges. Every aligned layout beta_e=kappa_e alpha_e is itself an allowed three-profile layout. Consequently

    min_(64^30 padded layouts) K(theta,beta)
      =min_(64^10 aligned layouts) K(theta,kappa alpha).        (SR4)

This identity concerns a fixed common theta. It does not interchange `forall layout exists theta` with `exists theta forall layout`. Nor does it combine measures from different families: SR4 gives a uniform bound on a cap functional which is already a valid bound for each family's actual measure.

## 3. Exact pairwise polynomial representation

Set P_r(b)=alpha_r(b)-1 for each of the64 role codes r, where b is one of the fourteen leaf blocks. For support T define

    G_T(b)=mask(b) product_(q notin T)b_q(b).

The aligned grid is

    H_T(r)=G_T
      -sum_(e disjoint T) kappa_e alpha_(r_e) G_(T union e)
      +sum_(e,f disjoint and disjoint T)
         kappa_e kappa_f alpha_(r_e) alpha_(r_f)
         G_(T union e union f).                     (SR5)

The pair sum is unordered. There are no terms of degree three because V has five vertices.

Expand at alpha=1. Let H_T^0 be SR5 with every alpha equal to1, and put

    A_(T,e)=-kappa_e G_(T union e)
       +sum_(f disjoint e and T)
          kappa_e kappa_f G_(T union e union f)

for e disjoint T, and A_(T,e)=0 otherwise. Then

    H_T=H_T^0+sum_e A_(T,e)P_(r_e)
       +sum_(e,f disjoint T)
          kappa_e kappa_f G_(T union e union f)P_(r_e)P_(r_f).

Any selected query, mass, selector difference or linear combination of them is therefore exactly

    F(r)=C+sum_e U_e(r_e)
               +sum_({e,f} disjoint)V_(e,f)(r_e,r_f).          (SR6)

All coefficients are rational once theta is rational. The interaction graph is the Petersen graph on the ten edges of K5; its numerical prime weights are never permuted or replaced.

The14-block representation is exact for the chosen block-constant theta. Reduced selector coefficients are obtained by summing the original selector coefficients over each block. Duplicate selector vectors may be removed, but no genuinely different selector may be omitted without an upper-bound certificate.

## 4. Anchor selectors plus an explicitly bounded regret

Choose any fixed selector k_j^0 for each j. For efficiency one may use the selectors active at the concrete reference layout

    (9,11,9,9,27,18,18,27,27,27),

with code32R+8C+4I+J and lexicographic numerical edges. The proof does not require those selectors to remain active at any other layout, or even to be optimal at the reference layout.

Define the pairwise reference polynomial and the difference polynomials

    E=(1-c)M-sum_j tau_j Q_(j,k_j^0),
    D_(j,k)=Q_(j,k)-Q_(j,k_j^0).

Since D_(j,k_j^0)=0, exactly

    K=E-sum_j tau_j max_k D_(j,k).                  (SR7)

This isolates the only nonpolynomial part, selector switching, as a sum of nonnegative regrets. It does not freeze a query's true maximizing selector.

## 5. A global upper bound on any difference polynomial

For a polynomial F=C+sum U_e+sum V_(e,f) on finite role domains, define

    R_(e,f)(r)=max_s V_(e,f)(r,s),
    R_(f,e)(s)=max_r V_(e,f)(r,s),
    Ubar_e(r)=U_e(r)+(1/2)sum_(f adjacent e)R_(e,f)(r).

For every actual pair (r,s), each of the two directional maxima is at least V_(e,f)(r,s). Their average is therefore also an upper bound, irrespective of the sign of V. Hence

    F(r)<=C+sum_e Ubar_e(r_e)
         <=B(F):=C+sum_e max_r Ubar_e(r).           (SR8)

All maxima are finite rational comparisons. If B(D_(j,k))<=0 on the full domain, that difference may be discarded globally. Floating tolerances are not an admissible reason to discard a difference.

## 6. Exact restriction to 64 covering branches

Fix the role of the first numerical edge {7,11} to r=0,...,63. These are64 disjoint exhaustive branches of all aligned layouts. Substitute the fixed role directly into SR6:

* add its unary value to C;
* for every incident pair factor, add the fixed row or column to the remaining neighbor's unary;
* remove those pair factors and set the fixed unary to zero.

This is an identity for every assignment of the remaining nine roles. More general fixed-role restrictions use the same rule, additionally adding fully fixed pair values to C.

For branch r define

    R_r=sum_j tau_j max(0, max_k B(D_(j,k)|r)).       (SR9)

Then R_r bounds the entire true selector regret on this branch. A difference discarded by a previously proved full-domain nonpositive bound need not be reconsidered.

## 7. An exact lower bound on the reference polynomial

Any representation SR6 yields the elementary lower bound

    L(E)=C+sum_e min_r U_e(r)+sum_(e,f)min_(r,s)V_(e,f)(r,s).

It can be improved by one finite sweep of algebraically exact reparameterizations. On an edge (e,f), set

    W(r,s)=V_(e,f)(r,s)+U_e(r)+U_f(s),
    a(r)=min_s W(r,s),
    b(s)=min_r W(r,s),
    U_e'(r)=a(r)/2,
    U_f'(s)=b(s)/2,
    V_(e,f)'(r,s)=W(r,s)-a(r)/2-b(s)/2.             (SR10)

The sum of the affected three factors is unchanged pointwise. All other factors stay unchanged, so the full polynomial is unchanged. Moreover the new pair factor is nonnegative. If m=min W, the minima of the two new unaries are m/2 each and the new pair minimum is0, attained at any minimizer of W. Their new local lower bound is thus m, at least the previous sum of the three separate minima. Each update preserves the polynomial and cannot weaken L.

Use one fixed sweep through the inherited unordered disjoint-edge pairs, omitting factors removed by the branch restriction. No convergence or optimality claim is needed. Let L_r be the elementary lower bound after this sweep. It is an exact lower bound for E throughout branch r.

An integer implementation may instead use any explicitly chosen rational messages in place of a/2,b/2, define the residual factor by exact subtraction, and recompute all minima. The resulting bound remains valid by pointwise preservation; matching the displayed half-minimum procedure is only needed to reproduce its numerical witness.

## 8. The finite certificate and source conclusion

The certificate obligations are now only

    for every r in {0,...,63}, L_r-R_r>=gamma>0.      (SR11)

All pairwise minima/maxima range over at most64^2 entries, and every remaining unary extremum ranges over64 entries. No64^10 enumeration is required. The64 branch reports cover the entire aligned domain. By SR7--SR10 each branch gate is at least its displayed L_r-R_r; SR4 then extends the same common-theta bound to all64^30 padded layouts and hence all actual central pair residues and missing slots.

The ordinary actual-source construction and complete-height coefficient bounds from Reports604/606 apply separately to each actual family. The chosen common theta thins that family's one measure; mass, remaining-original deletions, all queries and the23/29/31 continuation refer to it. Thus

    head Haar >= (2673/138320) gamma.                (SR12)

The certificate proves every branch strictly exceeds gamma=1/2000.
The smallest branch is role10, with exact lower bound

    8265813165441634135894893733190873
    /16260088821693963150100927610880000000
    =0.0005083498162945771... >1/2000.              (SR13)

The decimal is only a display. Multiplying the exact threshold by
2673/138320 gives a value greater than1/104000. Thus every admitted
actual family has complete ten-prime survivor Haar mass greater than
1/104000. Additional9q^2/25q^2 labels, support-four augmentations, exterior
branches and arbitrary pure/star data are outside this statement.

## 9. Reproducible exact certificate

The [producer](../../frontier/cover-geometry/all_pair_roles_certificate.py)
and [data](../../frontier/cover-geometry/all_pair_roles_certificate.json)
use only the Python standard library. Run

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/all_pair_roles_certificate.py

The producer pins Report606's producer and data, and through them the
Report604 source and complete coefficient arrays. It reconstructs the
strict box, complete selectors, role polynomials, branch substitutions,
selector-difference bounds and one-sweep lower bounds. No optimizer,
floating phase sample or exploratory program is a proof input.

The single14-entry thinning witness has denominator2^24 and numerators

    (10694693,12456216,14611741,16777216,
     11557478,11557478,10892491,14421682,13813346,
     6837092,8804584,6418709,10892491,8862779).

Its blocks are those of Report606. The511 fixed anchor selectors are
stored explicitly; they are legitimate menu entries, not a claim that
one selector remains optimal everywhere. Of3936 alternative-selector
differences,450 survive exact full-domain pruning;351 of511 queries need
no switching allowance. All discarded alternatives have nonpositive exact
upper bounds, with no floating tolerance.

For each rational pairwise polynomial the producer uses one common
integer denominator. Its lower-bound messages are floor(row minimum/2)
and floor(column minimum/2) in numerator units. Subtracting the messages
from the pair factor preserves the polynomial exactly. Signed floor
rounding is harmless because the elementary lower bound is recomputed
after the exact reparameterization; no convergence assertion is used.

All24 named predicates, evaluated3441 times, pass under-O with explicit
failure branches. The retained data includes every branch's reference
polynomial lower bound, selector-regret upper bound, gate lower bound and
Haar lower bound. Finite arithmetic verifies these witnesses. SR4 and
SR7--SR12 supply the proof that the64 branch bounds cover every actual
pair-role layout while comparing one actual source per family.
