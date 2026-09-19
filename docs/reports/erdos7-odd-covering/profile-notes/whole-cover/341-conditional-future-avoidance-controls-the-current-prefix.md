[Index](../../marked_head_profile.md) · [Original prefix completion](340-whole-cover-completion-constrains-original-prefix-loads.md)

# Conditional future avoidance controls the current prefix

The useful mature input is Hough–Nielsen **Theorem 4**, especially its conditional congruence-class bound (6), not only its uncovered-density bound (5). Its hypotheses allow multiple forbidden residues at one residual modulus. This permits a literal reduction of one original family's future classes on the same old point and current prefix. It does not supply a uniform supersolution or positive mass of successful old points.

## Verified source

Robert D. Hough and Pace P. Nielsen, *Covering systems with restricted divisibility*, Duke Mathematical Journal **168** (2019), 3261–3295, DOI <https://doi.org/10.1215/00127094-2019-0058>.

The inspected primary manuscript is <https://arxiv.org/pdf/1703.02133v2>, dated 8 August 2018. Theorem 4, equations (5)–(6), is on printed/PDF page 4. Its proof from the clique Lovász local lemma is in Section 4, pages 7–9. Theorem numbering here refers to this manuscript; the final journal edition was not inspected.

Let N be a finite set of moduli n>1, with prime factors in P. For each n let A_n be a set of residues modulo n. Suppose finite nonnegative weights ξ_q satisfy

    ξ_q >= sum_(n in N:q|n) (|A_n|/n) product_(r|n)(1+ξ_r),     (HN1)

for every q in P. Put

    B = sum_(n in N) (|A_n|/n) product_(r|n)(1+ξ_r).

For uniform integers modulo lcm(N), write F for avoidance of all A_n. The theorem states

    Pr(F) >= exp(-B) > 0,                                      (HN2)

and, for every n in N,

    max_b Pr(z=b mod n | F) <= exp(sum_(q|n)ξ_q)/n.              (HN3)

Empty residue sets are permitted: the paper's setup explicitly extends absent events by the empty set, and all terms of (HN1)–(HN2) for such an event are zero. Therefore one can append an empty test modulus without changing the event or costs. If it enlarges the period, uniform lift preserves the relevant probabilities.

The preceding theorem about a modulus divisible by 2 or 3 is a separate application. **Theorem 4 itself has no restriction to primes greater than 3 and no single-residue or distinct-original-modulus hypothesis.**

## Exact same-old, same-prefix pullback

Use the notation of 340. Fix a genuine old survivor x modulo Q_<p and a literal depth-t prefix J=j mod p^t, with 0<=t<=H. Let Q be the full original period and set

    D = Q_<p p^t,
    b = CRT(x mod Q_<p, j mod p^t).

The map

    z mod (Q/D) -> b + Dz mod Q

is a bijection onto this fixed old/prefix fibre, transporting uniform probability to its relative Haar law.

An original future label i is a_i mod d_i with

    d_i = g_i p^e_i s_i,  g_i|Q_<p,  s_i>1,

where every prime of s_i exceeds p. Define

    h_i = gcd(d_i,D) = g_i p^min(e_i,t).

The label is compatible precisely when h_i divides a_i-b. If incompatible it contributes no event. If compatible its pullback is one residue

    m_i = d_i/h_i = p^max(e_i-t,0) s_i > 1,
    r_i = inverse(D/h_i mod m_i) * ((a_i-b)/h_i) mod m_i.       (P1)

The inverse exists since gcd(D/h_i,m_i)=1. The modulus m_i divides Q/D. This formula keeps the actual original residue, not just an exponent vector.

For each residual modulus m, form the **set**

    A_m = {r_i : i compatible and m_i=m}.                      (P2)

Distinct original labels remain in the pullback table. Equal (m,r) pairs define the same forbidden event and may be merged for this set-union calculation; distinct residues at the same modulus remain separate elements of A_m. This does not turn the residual family into a distinct-original-label family. In particular

    sum_m |A_m|/m <= sum_(compatible original i) 1/m_i
                      = p^t F_J(x).                          (P3)

The left side still counts overlaps between different moduli. The HN dependency calculation, rather than merely (P3), handles those overlaps.

## Conditional cylinder bound and noncoverage density

If the compatible future collection is empty, take B=0 and all weights zero directly: future avoidance is the entire fibre. This avoids any convention about the least common multiple of an empty collection.

Let h=H-t. For h>=1 append the empty residue set modulo p^h to (P2). Include p in P and assign it a finite weight ξ_p satisfying (HN1). If no compatible future label has e_i>t, the new p constraint is zero and ξ_p=0 is allowed.

HN2 makes conditioning on future avoidance legal. HN3 at n=p^h gives

    Pr(z=r mod p^h | future avoidance,x,J) <= exp(ξ_p)/p^h.    (P4)

The current p-coordinate inside J is b+Q_<p p^t z modulo p^H. Since b agrees with j modulo p^t and Q_<p is a unit modulo p, its individual depth-H leaves correspond bijectively to residues z mod p^h. Thus (P4) also bounds every current leaf. Let

    c_J(x)=p^t a_J(x)

be the relative Haar proportion of J occupied by current classes. The current forbidden event depends only on this p-coordinate, so summing (P4) over its leaves gives

    Pr(current forbidden | future avoidance,x,J)
        <= exp(ξ_p) c_J(x).                                  (P5)

This statement is under the **same relative Haar law conditioned on the actual future union**. It does not replace the physical or killed measure in 340.

For any original family, let U_J(x) be the absolute current/future Haar mass in J missed by all earlier, current and future classes. Earlier classes miss because x is a genuine old survivor. Combining HN2 and P5 yields

    U_J(x) >= p^-t exp(-B)
                    [1-exp(ξ_p) p^t a_J(x)]_+.               (P6)

Indeed, if d is the relative probability of future avoidance and v is the conditional current-forbidden probability, then U_J=p^-t d(1-v), d>=exp(-B), and 1-v>=[1-exp(ξ_p)c_J]_+.

Under a whole-cover hypothesis U_J(x)=0. Since exp(-B)>0, (P6) implies

    a_J(x) >= p^-t exp(-ξ_p).                                (P7)

This is stronger than the bound p^-t exp(-B) obtained solely from HN2 whenever ξ_p<B. Large future loads involving only other primes do not directly enter this current-coordinate factor.

If h=0, J is a single current leaf. Its current-forbidden indicator is constant on all future coordinates. Positive future avoidance forces that indicator to be one under whole coverage, so a_J=p^-t. For arbitrary families P6 holds with ξ_p=0. There is no need to introduce the invalid modulus p^0=1 into Theorem 4.

To use P7 in CP5–CP6, one needs certificates for **every depth-t prefix at the same old x**. For example, if an old set E admits such certificates with ξ_p(x,J)<=K for all J, then

    m_t(x) >= p^-t exp(-K),  x in E,

under whole coverage. In the full-Haar clipped transfer of340, this yields a Gamma correction at depth t>=1 of at least

    (2t+1) min(1,delta/(1-delta)) p^-t exp(-K) eta(E).          (P8)

The incoming physical law mu and killed submeasure eta are unchanged. The conditional future-survivor law is used only to prove the pointwise P7; old points are not reweighted by future-survivor density or by certificate count. A positive numerical correction needs eta(E)>=w>0 under that actual same-chain killed submeasure. A collection of unrelated successful x,J pairs is insufficient. No uniform K,w for all hypothetical distinct odd covers has been proved here.

## A noncoverage test needs only successful prefixes

The all-prefix condition above is specific to a lower bound for m_t. It is not required to use P6 directly. Fix one depth t and, for each old x in R, let C(x) be any subset of its depth-t prefixes with verified HN certificates. All these old and prefix spaces are finite. For any finite nonnegative old measure eta supported on R, set

    L_eta = integral sum_(J in C(x)) p^-t exp(-B(x,J))
                [1-exp(xi_p(x,J)) p^t a_J(x)]_+ d eta(x).    (P9)

Because prefixes at that depth are disjoint, P6 gives

    (eta times Haar_Y times Haar_Z)(uncovered) >= L_eta.

Thus L_eta>0 proves that an actual uncovered integer exists by finite CRT. One successful pair x,J with positive eta({x}) and a strictly positive bracket is sufficient; certificates on other prefixes are unnecessary. This auxiliary product measure is explicitly different from the future physical/killed chain. Its numerical mass is a full Haar density only when eta is the appropriate old Haar restriction. For the existence conclusion no substitution between those measures is needed. No universal positive L_eta has been established.

## Explicit strict improvement over the raw prefix union bound

Take current p=5, height H=2, old carrier Z/3Z. Use the following 146 original classes:

- current class 25 mod75;
- mixed future class 0 mod175;
- 0 modq for each of the 144 primes 11<=q<=857.

All original moduli are distinct, odd and greater than one. The family is irredundant on its union; the checker supplies one actual private integer per original class. It is a noncover: integer15 misses all 146 classes.

Fix old x=0 mod3 and J=0 mod5 at depth t=1. The current class has old residue1, so a_J(x)=0. The future load from 340 is

    F_J(x) = 1/175 + (1/5) sum_(11<=q<=857 prime)1/q > 1/5,    (E1)

since the prime reciprocal sum is approximately 1.000314600914586. Thus the positive part of CP2's raw deficit is zero.

The arithmetic parameter is N=15z. The mixed future class becomes 0 mod35; the pure future classes become 0 modq. Append the empty test event modulo5. Choose

    ξ_5=ξ_7=1/32,  ξ_q=1/(q-1) for 11<=q<=857.

The two mixed constraints have

    G_5=G_7=(33/32)^2/35=1089/35840,
    ξ_5-G_5=ξ_7-G_7=31/35840>0.

Each pure q constraint is an equality. This is an exact rational HN certificate. Its total cost is

    B=1089/35840 + sum_q 1/(q-1).

The exact relative future-hole probability is

    (34/35) product_q (1-1/q)>0.                              (E2)

Conditioned on future avoidance, the remaining p digit has probability 3/17 at digit0 and 7/34 at each other digit. The entire pure-q product cancels in these conditional probabilities.

Hence P7 would require

    a_J >= exp(-1/32)/5 > 31/160,

if this were a whole cover, while its actual a_J is zero. Without a whole-cover premise, P6 directly gives a strictly positive uncovered prefix mass exp(-B)/5. The exact mass is E2 divided by5. This diagnostic shows a strict gain over CP2 without repeated residual events; it is not a new unrestricted noncoverage theorem.

The [standard-library checker](../../frontier/whole-cover/hn_current_prefix.py) reconstructs all inputs, verifies 146 rational prime constraints, checks 21,316 private-witness congruences, and separately checks the general arithmetic pullback on 279 old/prefix fibres using 415,800 individual membership comparisons. The latter fixture includes both coincident residual events and different residues at the same residual modulus. All checks use explicit exceptions and remain active with `python3 -I -S -O`. The [canonical certificate](../../certificates/source_norms/hn_current_prefix.json) records the exact inputs and results. Run `python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/whole-cover/hn_current_prefix.py --check`; a copied entrypoint accepts `--base /path/to/erdos7-odd-covering`. Exponential bounds are consequences of the cited theorem and elementary inequalities, not claims of finite numerical verification.

## Private-witness and other literature boundary

The same theorem can quantify a private set **conditionally**. Restrict all other classes to a target original AP a_t+d_t Z. A compatible other class pulls back to modulus d_i/gcd(d_i,d_t) and the corresponding solved residue. If the target is essential, no compatible modulus is1. After grouping residual events, an HN certificate bounds the relative density of the private set below by exp(-B), hence its full Haar density below by exp(-B)/d_t. This does not automatically give positive mass under a source law that may omit its old projection.

BBMST, *On the Erdős covering problem: the density of the uncovered set*, <https://arxiv.org/pdf/1811.03547>, Theorem3.1 and Lemma3.5 (pp.7,10–11), provide an additional measure comparison: a proven positive survivor mass under their specific distorted law gives an explicit Haar-density lower bound. The statement does not reverse to turn arbitrary Haar-positive witness sets into positive killed/source mass. Their Theorem1.1 also requires sufficiently large distinct residual moduli plus a weighted reciprocal budget; residual restriction need not preserve those hypotheses. HN's multiple-residue Theorem4 is the direct match here.

The current official problem page <https://www.erdosproblems.com/7>, accessed 2026-09-19, remains marked open and cites Hough–Nielsen and BBMST for the factor2-or3 and lcm9-or15 restrictions. No assertion above removes any hypothesis from those results or closes the unrestricted problem.

## Conditional union reduction and certified future majorants

HN feasibility depends on the events presented to the criterion. Even when
all original classes are irredundant, conditioning on one old point and
one current prefix can make a residual event contained in another.
Deleting such an event is legitimate for that conditional union. It does
not delete the corresponding original class from the original family.

More generally, fix the same old survivor x and current prefix J used
above. Let V_J(x) be the actual future forbidden union and let M_J(x)
be a union of auxiliary arithmetic-progression events, each with modulus greater than one, interpreted on the same fibre carrier or a common uniform lift, with

    V_J(x) subset M_J(x).                                      (MJ1)

One sufficient certificate for MJ1 assigns every compatible ORIGINAL
future label to an auxiliary class containing its residual class. For
residual a mod m and auxiliary b mod n, this is the check
`n divides m` and `a=b mod n`. Multiple auxiliary residues at one modulus
are permitted. Keep this map from original labels; an auxiliary event
is not a new original label or a claim of original-modulus distinctness.
Exact conditional union reduction is the special case of equality in MJ1.

Apply Hough--Nielsen Theorem4 to M_J, including the empty current-leaf
test modulus when needed. Write B_J and xi_(p,J) for this certificate's
cost and current-prime weight. The surviving set of the majorant is a
subset of the actual future-surviving set. Consequently its intersection
with current avoidance is a subset of the ACTUAL uncovered set, and

    U_J(x) >= p^-t exp(-B_J)
                 [1-exp(xi_(p,J)) p^t a_J(x)]_+.                (MJ2)

Only this lower bound is asserted: actual future avoidance and majorant
avoidance generally have different probabilities. Under whole coverage,
MJ2 still forces `a_J(x)>=p^-t exp(-xi_(p,J))`. The auxiliary HN law is
used to prove the pointwise inequality; it does not reweight the physical
chain or its killed old submeasure.

The majorant version of the pointwise bound can be inserted into P9 on any certified subset of prefixes. The all-prefix requirement remains specific to the separate Gamma correction.

## An irredundant low-rho head with a conditionally redundant future

Keep precisely the204 original classes of339's N=12 benchmark. Its
complete357 carrier is unchanged. Add the current original class

    1 mod11^12,

and the following21 future original classes, specified by CRT:

    0 mod11^e, e+1 mod13              for e=0,...,10;
    0 mod11^11, 0 mod13;
    0 mod11^e, 0 mod13, e mod17       for e=0,...,8.            (MJ3)

All226 full original moduli are distinct, odd and greater than one.
Every new class ends at11,13,or17 and has no3,5,or7 factor. Therefore
all original head labels, all full head heights, qJ, S, S0 and rho,
and the same-chain measure immediately before prime11 are unchanged.
The source stays at

    delta=0.00003388634450980418...,
    rho=0.05833338038722376...,

inside339's remaining region. No extension of the excluded rho>=1/10
region is used.

The combined family is irredundant on its union. A head private witness
extends with11-coordinate2 and13-coordinate12, avoiding every added
class. For a new class, use339's actual uncovered head point. A pure
future class has its prescribed13 residue,11-coordinate0 and17-coordinate16.
For the mixed class at depth e, use13-coordinate0,17-coordinate e and
11-coordinate11^e when e>=1, or2 when e=0. These points miss the depth11
pure class at13-coordinate0 and every other mixed class. The current
class has a private extension with13-coordinate12. These are CRT
constructions of genuine private integers, not only noncontainment
arguments. The full family is still a NONCOVER: the uncovered head point
with11-coordinate2 and13-coordinate12 avoids every class.

Now take p=11,H=12,t=11 and J=0 mod11^11. For EVERY old survivor x,
all p-conditions in MJ3 hold. In the actual remaining13/17 coordinates,
the literal residual presentation is

    A_13={0,...,11},
    A_221={z:z=0 mod13 and z in{0,...,8} mod17}.                (MJ4)

These are the actual integer's remaining13/17 coordinates, rather than P1's affine parameter z. The coordinatewise CRT relabelling is a uniform bijection; the event cardinalities and containment relations are unchanged. This presentation is independent of the old point. The current class misses J, so
`a_J(x)=0`. The literal HN presentation has no finite nonnegative
supersolution. Indeed, putting X=xi_13 and Y=xi_17, its constraints include

    X >= (12/13)(1+X)+(9/221)(1+X)(1+Y),
    Y >= (9/221)(1+X)(1+Y).                                  (MJ5)

The first implies X>=12. The second then gives Y>=9/8. Dividing the
first by1+X and using X/(1+X)<1 also gives Y<8/9, a contradiction.
This is a symbolic infeasibility proof; the numerical checker verifies
the exact cardinalities and rational coefficients used in it.

Every residual event in A_221 is already contained in the q=0 event
of A_13. Removing those nine events preserves the conditional union
EXACTLY. The reduced family has a certificate

    xi_13=12, xi_11=0, B=12,

with an empty test event modulo11. Its conditional current-leaf
probabilities are at most1/11. The exact residual hole is1/13; HN also
gives the valid lower bound exp(-12). Thus MJ2 proves, under any incoming
eta from the unchanged head with eta(R)>0,

    integral U_J d eta >= 11^-11 exp(-12) eta(R) > 0.          (MJ6)

The same twelve13 residues form a GLOBAL future majorant for MJ3,
with a direct containing class assigned to each original label. Outside
this chosen J it need not equal the actual future union; MJ1--MJ2 and P9 retain
the correct inequality direction.

This example shows that full-original irredundancy does not justify
keeping every event in a conditioned HN presentation. It also shows how
an exact residual reduction or a certified majorant can repair that
presentation without changing the source measure. It supplies no
uniform majorant, no uniform budget, and no solution of the unrestricted
covering problem.

The [standalone checker](../../frontier/whole-cover/hn_majorant_reduction.py) first reruns the
existing339 source producer and compares its complete result with the
canonical multipart-aware certificate. It then checks51,076 private
witness congruences against all226 original classes, all50,850 ordered
containment pairs, and2,431 actual conditional CRT points for the exact
union reduction. The [canonical certificate](../../certificates/source_norms/hn_majorant_reduction.json) retains the original-label majorant
map and the exact HN contradiction coefficients. Every check remains
active under `python3 -I -S -O`; no new Lean declaration is asserted.

Run `python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/whole-cover/hn_majorant_reduction.py --check`; a copied entrypoint accepts `--base /path/to/erdos7-odd-covering`.

## Conditional Haar queries can use only conflicting residues

Scott--Sokal, [arXiv:cond-mat/0309352v2](https://arxiv.org/pdf/cond-mat/0309352v2),
Theorem1.2 and equation(1.8), printed/PDF page7, give the lopsided local
lemma and its conditional avoidance bound. Theorem4.1, equation(4.3),
page50, gives the corresponding Shearer-polynomial bound. These apply
directly to the original Haar law conditioned on avoidance. The query
bound in [problem-details16](../../problem-details/16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md) concerns a resampling terminal law; that law
is not substituted here.

Fix the genuine old survivor x and current prefix J of P1. Keep each
compatible future original label as the atomic event `A_i={z=r_i mod m_i}`.
If using P2, split its multi-residue sets back into atomic events. Join
distinct vertices precisely when

    i~j iff gcd(m_i,m_j) does not divide r_i-r_j.              (CQ1)

Use P1's complete residual carrier Q/D, including every remaining current p digit. If starting with only the future-event period lcm(m_i), uniformly lift it to the common period with the query modulus d; this preserves the future-event probabilities. For a canonical test `T={z=b mod d}` on that carrier, let

    N(T)={i:gcd(d,m_i) does not divide b-r_i}.

These are exactly conflicting partial assignments of independent
prime-adic digits. To verify the weak dependency condition, force the
digits of any canonical E to their prescribed values. This produces
Haar conditioned on E. Every compatible event that held before forcing
still holds afterwards. Thus, for any set C of compatible events,
`Pr(avoid C|E)<=Pr(avoid C)`, and hence
`Pr(E|avoid C)<=Pr(E)` whenever the conditioning is defined.

If one set of weights `0<=u_i<1` satisfies

    1/m_i <= u_i product_(j~i)(1-u_j), for every i,

the cited conditional local lemma implies

    Pr(F)>=product_i(1-u_i)>0,
    Pr(T|F)<=(1/d) product_(i in N(T))(1-u_i)^(-1),            (CQ2)

where F avoids all future events. Indeed, with `C=V minus N(T)`, bound
`Pr(T|F)` by `Pr(T|avoid C)/Pr(avoid N(T)|avoid C)` and apply equation(1.8)
to the denominator. This uses the same valid weights throughout;
different certificates must not be spliced into one product.

More generally put

    Z_U=sum_(I independent in U)(-1)^|I| product_(i in I)(1/m_i).

If every induced Z_U is positive, Theorem4.1(4.3) gives the denominator
bound `Pr(avoid N(T)|avoid C)>=Z_V/Z_C`, so

    Pr(F)>=Z_V>0,
    Pr(T|F)<=(1/d) Z_(V minus N(T))/Z_V.                      (CQ3)

Decompose the actual current forbidden union inside J into disjoint
canonical prefixes T. Their relative Haar masses are `Haar_J(T)`;
full current leaves are always a permissible decomposition. Summing CQ3
under this same conditional law gives the direct noncoverage estimate

    U_J(x)>=p^-t [Z_V-sum_T Haar_J(T) Z_(V minus N(T))]_+.     (CQ4)

For clarity, if s denotes the sum in CQ4 and h=Pr(F), then the conditional current-union probability is at most s/Z_V. Hence U_J>=p^-t h[1-s/Z_V]_+>=p^-t[Z_V-s]_+; no bound on an unconditional intersection is substituted.

A strictly positive right side at one genuine x,J proves an uncovered
integer by CRT. An all-prefix condition is unnecessary for this test.
Any subsequent integration uses the original old measure, without
reweighting by future-survivor density. Feasibility remains an input;
the complete-star failure of universal conflict-Shearer feasibility in
problem-details16 is not removed.

On the146-class diagnostic's fixed fibre all future events are `0 mod35`
or `0 modq`. Their conflict graph is empty, so `u_i=1/m_i` satisfies CQ2.
For remaining current digit0 there are no query neighbors, giving cap1/5.
For each nonzero digit, only `0 mod35` conflicts, giving cap7/34. The
actual probabilities are3/17 and7/34. Both caps are below the HN cap
`exp(1/32)/5`; for the larger one use `exp(1/32)>33/32>35/34`.
The current union is empty at that old point, so these finer leaf caps
do not improve its already-unit current-union deficit. This is a check
of residue sensitivity, not a claim of universal progress.

## The literal HN failure admits a conflict-Shearer certificate

Retain the226-class construction coupled to the actual339 head and all
21 residual events at `J=0 mod11^11`. They are

    A_a={z=a mod13}, a=0,...,11,
    B_j={z=0 mod13,z=j mod17}, j=0,...,8.

No event is deleted. The A vertices form a clique; the B vertices form
a clique. Every B conflicts with A_1,...,A_11 and is compatible with A_0.
Thus the literal graph is K_11 joined to the disjoint union of A_0 and
K_9. Charges remain1/13 and1/221.

Every induced graph has k nonzero A vertices, an indicator delta for
A_0, and r B vertices, where `0<=k<=11`, `delta in{0,1}`, `0<=r<=9`.
Its exact independence polynomial is

    Z_(k,delta,r)=(1-delta/13)(1-r/221)-k/13.                 (CQ5)

The product counts choices from A_0 and the B clique; a nonzero A
vertex excludes every other vertex. CQ5 decreases in all three parameters
on these ranges. All240 induced types are therefore positive, with

    min Z_U=Z_V=(12/13)(212/221)-11/13=113/2873>0.           (CQ6)

The remaining current11 digit has no conflicting future neighbor, so
CQ3 gives cap1/11. The original current class `1 mod11^12` misses J.
CQ4 consequently gives missed current/future mass at least
`11^-11*113/2873>0` at every old point surviving the actual339 head.
Direct counting gives future-hole probability1/13 and missed mass
`11^-11/13`; every current conditional digit has probability1/11.

This supplies a second mature criterion on the unchanged residual
presentation where literal HN failed. The exact-union reduction already
proved noncoverage of this same family. No additional unrestricted
family is excluded by this diagnostic.

The same [majorant checker](../../frontier/whole-cover/hn_majorant_reduction.py) reconstructs all210 literal CRT pairs from the producer's
21 residual rows, checks the201 conflict edges, and compares CQ5 with
an independent deletion recurrence for all240 induced types. It also
checks all2431 residual CRT points and all11 current conditional digit
probabilities. Original-label provenance, private witnesses and the339
source remain verified by the same original-family producer.
