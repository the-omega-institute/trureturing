# A common upper-tail comparator sharpens the existing source moments

On the SAME actual shallow source mu23 used in Reports725,728,730 and735,
every complete old query L is bounded in increasing-convex order by one
explicit finite law Y. Consequently the simultaneous bounds improve to

    E_mu23 L <=354870451028/26915276115,
    E_mu23 L^2 <=1940069387744/8971758705,
    E_mu23 L^3 <=31390970044192/6211217565.                 (UT1)

Their approximate values are13.184722665,216.241815182 and5053.915712288.
The shape-paired fourth moment from [Report735](735-shape-specific-fourth-moments-on-the-unchanged-shallow-source.md) remains the stronger bound

    E_mu23 L^4 <=4005807477705/19895792.                   (UT2)

All four estimates refer to one unchanged actual survivor law, with
complete freely phased numerical-divisor queries. The construction
retains the shallow old caps v3<=2 and vp<=1 for p=5,7,11,13,17,19,23.
It does not supply an unrestricted-height head or by itself prove
five-direction carving positivity. This is ordinary mathematics with
exact finite controls, not new Lean verification.

## 1. The inherited premise is a full convex comparison on the same law

[Report1, section *A single improved full comparator*](../../001-064/01-survivor-reduction.md#a-single-improved-full-comparator), proves that on one
uniform actual pruned315 survivor law mu315 every complete query is
dominated in increasing-convex order by the SAME comparison variable X:

| x | 1 | 2 | 3 | 4 | 5 | 6 | 8 | 12 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| P(X=x) |581/6966|3031/6966|146/1053|425/2106|10/1443|45/481|1/37|1/74|

Thus E_mu315 h(L)<=E h(X) for every increasing convex function h on the
nonnegative range. This is stronger than a list of monomial moments.
The source explicitly permits its direct square and full hinge profile
to be used simultaneously. Report728 TC4 cites precisely that same-law
premise, and Report1's pure11 extension already gives the one-prime
convex-comparison and conditional upper-tail construction used below.

The head source is inherited; the present exact consumer pins its
certificate and checks that this X reproduces its recorded hinge knots.
It does not reexecute the earlier geometric enumeration or present its
own table arithmetic as a new proof of the head theorem.

## 2. Transport the complete convex comparison through the pure roots

Suppose every complete old query under an actual probability law nu
is dominated by a comparison variable Z. Append a fresh first-level
prime p, removing its actual pure forbidden digit. The new actual law
before mixed deletion is nu times the uniform law on its p-1 pure-live
roots. For an arbitrary complete enlarged query, write its load as

    L(x,z)=A(x)+B_z(x).

A is a complete old query. The sum of the nonnegative increments B_z
over the pure-live roots is bounded above by a complete old query B;
an absent or excluded phase only removes a nonnegative term.

Convex concentration gives, for increasing convex h,

    sum_(z pure-live) h(A+B_z)
       <=(p-2)h(A)+h(A+B).                               (UT3)

For two increments this follows from increasing increments of a convex
function; combine increments successively, then use monotonicity to
replace their sum by B. This argument does not require h to be
nonnegative: the unchanged baseline copies are kept on both sides.

Pointwise Jensen gives

    h(A+B)<= [h(2A)+h(2B)]/2.

Both old query blocks are controlled by the same old law's complete
comparison, and h(2x) is again increasing convex. After expectation and
averaging the p-1 roots,

    E h(L) <=(1-1/(p-1))E h(Z)+(1/(p-1))E h(2Z).        (UT4)

Define an AUXILIARY variable D_p independently of Z by

    P(D_p=2)=1/(p-1),       P(D_p=1)=(p-2)/(p-1).

The right side is E h(Z D_p). Independence belongs only to this finite
comparison representation; no independence of actual A,B or source
coordinates is asserted.

Iterate for p=11,13,17,19,23. On the actual pre-mixed carrier sigma, which
is mu315 times the five pure-live coordinate laws, every complete query
is dominated in increasing-convex order by

    Z = X product_(p=11,13,17,19,23) D_p.                (UT5)

The256 auxiliary outcomes (eight X atoms and32 binary choices) combine
into23 distinct Z atoms. All original phases remain fixed, and every
query phase remains freely chosen per numerical label. No new actual
source is chosen separately for an h, a query or a moment order.

## 3. Condition once on the SAME actual mixed survivor

Let E be the actual survivor event after all mixed shallow originals
are removed from sigma. [Report725](725-one-common-shallow-carrier-admits-an-arbitrary-height-last-prime.md) and [Report728](728-one-common-shallow-source-supports-three-arbitrary-fresh-prime-heights.md) provide its six shape-specific
probability lower bounds

    1243487/13077504,
    7609619/64627200, 7609619/64627200,
    39317/253440,
    123881/887040, 123881/887040.

Their minimum is

    delta0=1243487/13077504.

The actual probability s=sigma(E) is at least delta0; it is not assumed
equal to delta0. The actual law is exactly the already used

    mu23=sigma conditioned on E.

For any increasing convex h and any constant a, the pointwise inequality
h(L)<=a+(h(L)-a)_+ gives

    E_mu23 h(L)
       <=a+(1/s)E_sigma[1_E(h(L)-a)_+]
       <=a+(1/delta0)E_sigma(h(L)-a)_+
       <=a+(1/delta0)E(h(Z)-a)_+.                       (UT6)

The last step uses that x -> (h(x)-a)_+ is increasing convex. This is
why the inherited FULL increasing-convex premise matters. Nonnegative
residuals justify replacing s by its lower bound and dropping1_E. The
actual conditioning event is fixed once for every query and every h.

The earlier raw-moment division E_mu23 L^k<=E Z^k/delta0 is the choice
a=0. It unnecessarily divides the baseline part by delta0. Formula(UT6)
allows that baseline to remain at its original scale.

## 4. One upper-tail law simultaneously works for every convex test

The exact Z law satisfies

    P(Z>8)=42911442037/636890791680
       <=delta0
       <=P(Z>=8)=44132998649/283062574080.               (UT7)

Define one AUXILIARY probability law Y by taking the upper delta0-mass
of Z, splitting the atom at8, then normalizing:

    P(Y=z)=P(Z=z)/delta0,     z>8,
    P(Y=8)=1-P(Z>8)/delta0.                              (UT8)

Both probabilities and the amount taken from the8-atom are valid by
(UT7). Y has no values below8.

Take a=h(8) in(UT6). Monotonicity gives

    E(h(Z)-h(8))_+
      =sum_(z>8)P(Z=z)[h(z)-h(8)].

This identity also holds when h is flat on some interval: terms above8
with h(z)=h(8) are simply zero. It does not require strict monotonicity.
Substituting(UT8) gives

    E_mu23 h(L)<=h(8)+(1/delta0)E(h(Z)-h(8))_+
                  =E h(Y).                             (UT9)

Thus the SAME Y bounds every increasing convex test of every complete
query on the SAME actual mu23. It is not a future survivor law and need
not be an actual distribution of any one query.

The following integers specify the entire law. Divide every numerator
by the common denominator242237485035:

| Y value | Probability numerator |
|---:|---:|
|8|70591716887|
|10|4617831060|
|12|99883711989|
|16|40776235983|
|20|676677240|
|24|19109010499|
|32|4156249250|
|40|48436920|
|48|2007332794|
|64|239722674|
|80|1695060|
|96|117799876|
|128|7286909|
|160|23220|
|192|3618837|
|256|90558|
|384|45279|

The numerators are positive and sum to242237485035.

## 5. Improved moment interface and retained fourth-order bound

Taking h(x)=x^k in(UT9) gives

| k | E Y^k | Approximate value |
|---:|---:|---:|
|1|354870451028/26915276115|13.184722665|
|2|1940069387744/8971758705|216.241815182|
|3|31390970044192/6211217565|5053.915712288|
|4|1089423903671104/5383055223|202380.220625707|

The first three are strictly below the previous common caps19,
2607189975/7283281 and906617738995/159166336. At fourth order the
Report735 bound4005807477705/19895792, approximately201339.432866,
is stronger than E Y^4 and remains valid on the identical source.
Therefore the usable first-four interface is(UT1)-(UT2), together with
the whole hinge and increasing-convex family from(UT9).

The comparison also passes to every finite-height padded support field

    C_J=sum_e alpha_(J,e)L_(J,e)+(1-sum_e alpha_(J,e)),

where alpha>=0 and sum alpha<=1. Jensen and(UT9) give

    E h(C_J)<=sum_e alpha_(J,e)E h(Y)
                    +(1-sum_e alpha_(J,e))h(1)
             <=E h(Y),                                 (UT10)

since Y>=8>=1 and h is increasing. Joint independence of these fields
is not asserted; they remain simultaneous functions on the one actual
source. The same Jensen argument preserves the separate fourth bound.

This invalidates treating the older scalar moment caps as the full
remaining interface. For a minimal finite check, the selected constant
load17 has moments17,289,4913,83521: all lie below the old mean/square/
cubic and Report735 fourth caps, but17 and289 exceed the new mean and
square bounds. Such a scalar model is not an actual congruence family.
Its purpose is to distinguish the strengthened interface from merely
reweighting the old four inequalities. A table satisfying only those
older inequalities cannot settle the current joint-feasibility problem.

The new common comparison supplies sharper inputs to carving or other
continuations. Positivity of a specific five-direction objective still
requires its own inequality or exact joint-feasibility argument; it does
not follow merely from displaying Y.

## 6. Exact controls and inherited boundaries

The [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_conditioned_convex_source.py) and its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_conditioned_convex_source.json)
pin two existing source files:

- The full head-profile piece
  `certificates/marked_head_profile_certificate.parts/content/012-deletion_weighted_comparison.json`,
  SHA256 `603a91b3d6f91d59b835deb9e0f0a8bd26148852f4e038dbacea6e5423634a5c`.
- The actual common-source retention result
  `frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_uniform_shallow.json`,
  SHA256 `afc7b9a8167cf22e67885e427c865c5daa844eb3664b6ff7b684be56e3168591`.

It reconstructs X and every source hinge knot, all256 comparator
outcomes, all23 Z atoms, the exact upper-tail quantile inequality,
all17 Y probabilities, all four moments and385 integer-hinge identities.
It also checks the strict first-three improvements, the stronger
same-source fourth bound, and the finite constant-load negative control.
All decisions use exact fractions.

An independent construction from the pure-prime generating polynomial
and greedy upper-mass extraction agrees with the same Y and moments.
The old source geometry and its common-law meaning remain inherited
ordinary premises. No new Lean proof, arbitrary-head-height extension,
five-direction positivity or unrestricted odd-cover resolution is
claimed by this comparison alone.
