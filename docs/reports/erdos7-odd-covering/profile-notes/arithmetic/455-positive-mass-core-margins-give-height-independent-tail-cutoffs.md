# Positive-mass core margins give height-independent weighted tail cutoffs

A core probability with a Haar-density bound uniform in the core heights, and a completion margin at every point of its support, can be extended through arbitrary finite outside-prime supports and heights with a cutoff independent of the core exponents. The resulting law retains that good core support, with a controlled change of core marginal; it need not retain an arbitrary prescribed marginal exactly. A fully deleted core fibre in the original arithmetic example below proves that this distinction is necessary.

The proof reuses the bounded-density and original-LCM moment method, the capped kernels of Chapter07, and report453's early/late ternary split. Its additional conclusion is the all-original-depth weighted completion bound with a core-height-independent cutoff, supplied with actual good sets from report454. These are ordinary proofs and exact arithmetic controls, not new Lean certification or a claim of public mathematical priority. Stronger existing noncoverage ranges in Chapter33 remain available.

## 1. Core law, original labels and the support-preserving conclusion

Let K and Q be positive integers with K odd, coprime to 3, and Q|K. Let H>=1 be finite, and let mu be a probability on Z/K. Assume

    mu({x})<=Lambda/K for every x,   Lambda>=1,           (BC1)

and that mu is supported on a declared good set A avoiding every original 3-free core class. The density bound is relative to Haar on the FULL original core. It implies mu(C)<=Lambda/d for every original or queried residue cylinder modulo every d|K, including intersections of differently labelled head cylinders.

Use the original-label family and cofactor events of [report453](453-prime-tail-conditioning-preserves-core-laws-at-unrestricted-support.md): a tail modulus is

    3^e a product_(p in T)p^f_p,
    a|Q, 0<=e<=H, nonempty T subset P, 1<=f_p<=J_p,

where P is a finite set of outside primes coprime to 3K, every J_p>=1 is finite, and each numerical modulus has at most one fixed original residue. No support-size or interaction-graph restriction is imposed. Define

    J1(Q)=sum_(a|Q)1/a,
    J2(Q)=sum_(a,b|Q)1/lcm(a,b),
    N=ceil(Lambda J2(Q)).

If all outside primes are at least an integer

    B>=3^256 N^3,                                       (BC2)

there is ONE probability nu on the full 3-free CRT product such that:

- it avoids all original 3-free core and tail classes;
- its core marginal is supported on A;
- its total original weighted tail completion is

      L_tail(nu)<=324 Lambda J1(Q)/B<3^(-250);           (BC3)

- with epsilon=108 Lambda J2(Q)(1+ln B)^2/B<3^(-240),

      nu_core(E)<=mu(E)/(1-epsilon),
      TV(nu_core,mu)<=epsilon.                          (BC4)

Here TV is the supremum over events, equivalently half the L1 distance. All events and all ternary depths use this one nu. The parameter epsilon bounds failure under the constructed joint capped law; it is not an asserted uncovered density under original Haar.

In particular, if ell_core(x)<=B_H-eta on A, with pure 3-powers excluded from ell_core and B_H=(3+3^(1-H))/2, that same pointwise bound remains valid after the marginal changes. Adding (BC3) costs at most 324 Lambda J1(Q)/B. No uniform-Haar claim on the final survivor set is made.

## 2. Averaging the original head intersections before conditioning

At largest outside prime p, put E_p=min(H,floor(log_3 p)) and regard all original depths e<=E_p as early. Run exactly the report453 threshold-1/2 normalized kernels at each actual core x. They are defined even when a fibre is completely forbidden. Write sigma_x for the outside law and

    sigma(x,y)=mu(x)sigma_x(y).

For any fixed head event C and any j prescribed outside cylinders, integrating the existing selected-coordinate bound over x gives

    sigma(C intersect outside cylinders)
       <=2^j mu(C) product p^(-f_p).                    (BC5)

History dependence and dependence on x are allowed: the outside bound holds uniformly at each fixed x before the integration. It does not assert independence of the core and outside coordinates.

Expand the square of the raw early forbidden mass at p over original label pairs. For two head labels a,b, incompatible original phases contribute zero; compatible phases define a cylinder modulo lcm(a,b), whose mu mass is at most Lambda/lcm(a,b). The sum over all head-label pairs is therefore at most Lambda J2(Q), rather than the unweighted inventory count tau(Q)^2. The original ternary depths still contribute at most (E_p+1)^2; coincident cofactor events do not erase their original labels.

With a_q=1/(q-1), report453's remaining exponent-pair expansion gives

    E_sigma alpha_p^2
      <=Lambda J2(Q)(E_p+1)^2 a_p^2
         product_(q in P,q<p)(1+6a_q+4a_q^2).           (BC6)

The factor 2 for a queried preceding prime is paid once even when that coordinate occurs in both originals. The current p-coordinate contributes the product of its two Haar cylinder sizes. No further head-inventory factor is introduced.

Apply the unchanged prime-product and summation estimates UT6--UT9. Let Good be the complement of the union of all early cofactor events. Then

    sigma(Good^c)<=108 Lambda J2(Q)(1+ln B)^2/B
                 =epsilon.                            (BC7)

At B*=3^256 N^3,

    1+ln B*<=513+3ln N<=513N,
    epsilon<=108*513^2/3^256<3^(-240).

For larger B, (1+ln B)^2/B decreases. Thus Good has positive sigma mass. Define nu=sigma(.|Good), conditioning the GLOBAL joint law once. Some individual core fibres may have no survivors at all. This construction remains defined because it needs only the positive global mass proved in (BC7).

Conditioning preserves the support A and gives the domination in (BC4). The full joint total variation from sigma is sigma(Good^c), and passing to a marginal cannot increase it. This proves the TV statement. Exact marginal preservation is not claimed.

## 3. Late original layers on the same final law

Equation (BC5), the density cap, and the single conditioning denominator give

    nu(C_(a,head phase) intersect j outside cylinders)
       <=2^j Lambda/[a(1-epsilon)] product p^(-f_p)
       <=2^(j+1) Lambda/a product p^(-f_p).             (BC8)

All early cofactor events have zero nu mass. At largest prime p the sum of the remaining weights is at most 9/(2p), just as in UT11. Summing (BC8) over all original head divisors now contributes Lambda J1(Q). Summing the preceding prime supports and applying UT7--UT8 gives

    L_tail(nu)<=324 Lambda J1(Q)/B.

Since J1<=J2 and Lambda J2<=N, (BC2) makes this smaller than 3^(-250). This retains arbitrary finite ternary depth H without a factor H. It proves (BC3), using the original cofactor residues and the same probability nu throughout.

For a fixed finite prime set P0 containing every prime divisor of Q, geometric sums give

    J1(Q)<=product_(q in P0)q/(q-1)=:M1(P0),
    J2(Q)<=product_(q in P0)q(q+1)/(q-1)^2=:M2(P0).     (BC9)

Indeed, for one prime, the pairs of nonnegative exponents with maximum h number 2h+1, so their infinite weighted sum is (1+1/q)/(1-1/q)^2. Consequently a height-independent Lambda gives a height-independent cutoff. Controlling Lambda, not merely naming a finite core, remains a genuine hypothesis.

## 4. Positive-mass core margins from report454

For P0={5,7,11,13}, the complete original e=0 survivor set S satisfies

    Haar(S)>=79/192,
    d mu_S/d Haar<=192/79,                             (BC10)

by Chapter19's existing 79/99 mixed-survivor bound and the product pure-domain bound 33/64. These apply at arbitrary finite core heights. Moreover

    M1=1001/576,    M2=7007/1440<5.

First assume h5<=3 OR h7<=2 OR h11<=1 OR h13<=1, the four height conditions of [report454](454-integer-first-layer-loads-give-core-margins-with-one-bounded-prime-height.md). Its same-law proof gives E_muS psi<=3-kappa with kappa=1/1050, psi>=0, and an integer first-layer count. Let

    A={x in S: psi(x)<=3-kappa/2}.

Markov's inequality gives

    mu_S(A)>=kappa/(6-kappa)=1/6299.

Every point of A has first-layer count 0 or 1, and the CH8 argument gives

    ell_core(x)<=3/2-1/4200   for every x in A.

Thus mu=mu_S(.|A) has Haar density at most 1209408/79<16000. This selects a positive-mass set for the current complete original configuration; it does not choose one set in advance of arbitrary future core phases.

Alternatively, let the COMPLETE original family have ternary height 1<=H<=5 and allow all four core heights to be arbitrary finite. From report454 CH10,

    V=(B_H-ell_core)_+ in [0,2],   E_muS V>1/1000.

For A={V>=1/2000}, the elementary bound

    E V<=1/2000+(2-1/2000)mu_S(A)

implies mu_S(A)>1/3999. On this A, ell_core<=B_H-1/2000; its conditional law has Haar density below 767808/79<16000. The H<=5 restriction includes pure 3-powers and all outside labels when this case is composed with the tail theorem.

In either case Lambda=16000 and N<=80000 are valid. Therefore the single cutoff

    B>=3^256 * 80000^3                                (BC11)

suffices, independently of all finite core and outside exponent heights. In the first case H is arbitrary finite; in the second case the whole-family H<=5 restriction remains. The weighted tail bound is less than 3^(-250), leaving a positive completion margin in either case. The [fixed early-phase family](456-a-fixed-original-phase-family-has-core-margins-at-all-heights.md) also supplies a good set at arbitrary core heights, allowing the smaller rounded density cap 85 and cutoff 3^256*414^3. Existing Chapter33 already provides stronger bare noncoverage ranges. The additional interface here is the original weighted completion law, on an actual good core support, at a cutoff independent of core exponents.

## 5. Why arbitrary fixed core marginals cannot have this cutoff

For any outside prime p>=7, p!=5, take Q=5^(p-1). Use the p original 3-free labels

    m_j=5^j p,  j=0,...,p-1,
    alpha_(m_j)=0 mod5^j,   alpha_(m_j)=j modp.         (BC12)

The moduli are distinct odd integers greater than one. At the core point x=0, the p classes cover all p outside leaves. Thus no law supported on the actual 3-free residual can have core marginal delta_0. There are no core deletions or core completion costs in this example. Since p can be arbitrarily large while the core has only one prime, no cutoff depending only on core prime count can guarantee preservation of EVERY supplied core marginal across arbitrary core heights.

This is not a covering system: for example the core point 1 with outside leaf 1 survives all (BC12) classes. It distinguishes exact preservation of an arbitrary marginal from the bounded-density, support-preserving conclusion above.

The finite control uses p=7, Q=5^6 and additionally one original late label 3^2*5^j*7 for each j, with head residue 0, outside residue j+1 mod7 and ternary residue 0 mod9. Its 14 numerical moduli are distinct. Start from Haar on Z/Q. The exact valuation partition has seven cells and 49 joint cells; the final global conditioning deletes the entire core-zero fibre but leaves global survival 109188/109375. The core marginal changes by TV=5797/3412125. Its early second moment is exactly J2(Q)/49=29293/765625, and its actual late weighted completion is 57619/982692. Forty-nine queried joint caps and 441 literal original CRT checks verify the interpretation under this one final law. This small prime does not satisfy (BC2); its control uses measured survival, not the asymptotic guarantee.

## 6. Reuse and the unrestricted boundary

[Chapter33](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md), SH5--SH12, already uses a full joint Haar density bound to control LCM moments. [Chapter08](../../problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md) distinguishes preserving a supplied marginal from constructing a dominated new marginal. Report453 supplies the all-original-depth early/late completion split and summation constants. The construction above composes those tools with a positive-mass version of report454's core margin; it does not introduce a new generic kernel, moment theorem or Lean wrapper.

The published source Balister--Bollobás--Morris--Sahasrabudhe--Tiba, [On the Erdős covering problem: the density of the uncovered set](https://arxiv.org/abs/1811.03547), uses normalized capped laws and exact congruence-intersection moments: see equation (5), Lemmas 2.1, 3.6 and 3.7, and the second-moment seed in section 6, equation (20). Those components do not by themselves state the all-depth weighted completion interface proved here. Its near-cover constructions do not conflict with a small failure probability under this constructed law; the latter is not a Haar uncovered-density estimate.

For a fixed finite prime inventory, repeatedly absorbing primes below the current cutoff necessarily terminates after at most one strict addition per prime, possibly with an empty tail. What is not supplied is a good-core theorem for the resulting arbitrary core, or a guarantee that a nonempty admissible tail remains. In particular, enlarging the four-prime core beyond 5,7,11,13 is not justified by (BC10). Neither the cutoff improvement nor (BC12) resolves unrestricted Erdős #7.

Exact controls: [program](../../frontier/cover-geometry/bulk_core_tail_lift.py) and [results](../../frontier/cover-geometry/bulk_core_tail_lift.controls.json).


```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/bulk_core_tail_lift.py
```
