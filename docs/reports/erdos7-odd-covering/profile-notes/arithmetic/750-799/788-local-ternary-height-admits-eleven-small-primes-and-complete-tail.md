# A local ternary-height restriction admits eleven small primes and a tail above1300

Let C be a finite family of pairwise-distinct odd numerical moduli greater
than one, each with one globally fixed residue. Let R be its set of actual
support primes at most1300, and assume |R|<=11. Let R0 consist of the smallest
min(9,|R|) primes in R. Suppose only the originals whose entire prime support
lies in R0 satisfy v3(m)<=1. Then C is noncovering. A constructed distorted
survivor measure has mass greater than1/40.

An original involving the tenth or eleventh small prime, or any prime above
1300, may have arbitrary ternary depth, other finite exponents, and mixed
support. There is no bound on the number of primes above1300. The mass1/40
is not a claim about Haar density of the final survivor.

This is an ordinary mathematical combination of [Report707's actual common
source](../700-749/707-shared-support-avoidance-closes-twelve-height-one-primes.md), a finite-prefix query identity, the existing pure-conditioned
continuation, and [Report734's same-source quartic tail](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md). It is not new Lean
verification or an unrestricted odd-covering result. In particular [Report528](../500-549/528-surviving-fibre-credits-control-arbitrary-phases-at-ternary-height-one.md)
already has the eight-prime local-height source and arbitrary29/31
continuation; the new use here begins with the nine-prime source.

## 1. The inherited nine-prime source retains higher ternary Haar digits

Initially take the benchmark old head

    P9=(3,5,7,11,13,17,19,23,29).

All its actual old originals have v3<=1. If the numerical label3 is absent,
adjoin one phase at that unused label for this source construction. Let
lambda3 be Haar conditioned on the two remaining ternary roots. These root
names do not change the original phases. For q in P9 minus{3}, let Sq be
the actual survivor of every pure q-power original and set

    lambdaq=Hq|Sq/Hq(Sq),       Cq=(q-1)/(q-2).

The finite distinct pure inventory gives Hq(Sq)>=(q-2)/(q-1), and hence
lambdaq(a mod q^j)<=Cq q^-j. Define the one product source

    lambda=lambda3 tensor product_q lambdaq.

Let U be the actual survivor of all old originals, and put

    alpha=lambda(U),       mu=lambda|U/alpha.

Report707 SS4 supplies the uniform ordinary source premise

    alpha>=alpha*=4945117/39037950.

It proves this for arbitrary fixed old phases and all finite nonternary
heights by the shared-label support response and its complete triangle
comparison. The source is fixed before any query; no maximizer can select
a different law.

Crucially, U depends on the ternary coordinate only through its first root.
Therefore the conditional higher ternary digits under mu remain independent
Haar, even though the first root can become correlated with every other
coordinate and the two roots need not retain equal mass.

Write Btr(mu) for the complete query-max sum, including the unit label, with
ternary exponent0 or1 and all nonternary exponents unrestricted. Report707's
same-source stop-loss bound is

    Btr(mu)<=8+H0/alpha<=8+H0/alpha*,                   (L1)

where the exact complete-tail hinge is

    H0=
      36645196186562338862630609094665977037308771636736172158282771192951
      /91259075188331710704228574683636183224582522412602232580056664218750.

This constant belongs to the auxiliary product with a ternary factor equal
to1 or2, each with probability1/2, and nonternary run tails Cq/q^j. It is
an outer convex comparison, not a product claim about mu.

## 2. Restore all later ternary query depths on the same source

For each3-free old modulus d, put Ae(d)=max_a mu(a mod3^e d). The Haar suffix
gives Ae(d)=3^(1-e) A1(d) for every e>=1. Set

    B0=sum_d A0(d),        B1=sum_d A1(d),

including d=1 and all nonternary heights. The exact all-depth query budget is

    Bfull(mu)=B0+(3/2)B1.

Each3d cylinder lies in a d cylinder, so A1(d)<=A0(d), and hence B1<=B0.
It follows that

    Bfull(mu)<= (5/4)(B0+B1)
             <=(5/4)(8+H0/alpha*)=:L
             =13.962428447433757...<14.                (L2)

The exact L is

    129126856543850023127314117640338874610874565841696281911913189017951
    /9248166035728768426468350854567289757356579420496010975363041782500.

This completion uses actual Haar suffixes. It would be false for an arbitrary
finer source with the same root marginal: normalized Haar on1 mod9 has
truncated ternary budget2 and complete budget7/2, larger than(5/4)*2.
Conversely a source on one ternary root with independent Haar suffix attains
the factor5/4. No equal-root-mass assumption is used in(L2).

More generally, if a prime p has Haar suffix above depth h, let Bj be the sum
of its depth-j query maxima over the other numerical cofactors. Then

    Bfull=sum_(j<h) Bj+[p/(p-1)]Bh,
    Btr=sum_(j<=h) Bj,
    Bfull<=[1+1/((p-1)(h+1))]Btr.                     (L3)

The proof is Bj>=Bh for j<=h and the geometric suffix sum. Independent Haar
suffixes at several coordinates allow successive use of the factors while
retaining all correlations in the low digits. The factor at ternary depth2
would be7/6; no suitable unrestricted depth-two old-source bound is proved
here.

## 3. Two additional actual primes can now use arbitrary ternary heights

Use the actual pure-survivor probabilities at31 and37, with their caps
Cq=(q-1)/(q-2). They avoid every pure new-prime original before the remaining
mixed deletion. Put

    b31=1/29, b37=1/35,
    s=b31+b37=64/1015,
    Q=(1+b31)(1+b37)-1=13/203.

An original using just one new prime and a nonunit old cofactor is charged
by that prime's complete b inventory times(Bfull-1); the old-unit case was
already excluded as a pure original. An original using both new primes is
charged by b31*b37 times Bfull, INCLUDING the old unit. Distinct full
numerical moduli guarantee at most one phase per exponent vector. No phase
is changed between these counts.

Thus the actual remaining union has mass at most

    (Bfull-1)s+Bfull(Q-s)=Bfull Q-s.

Deleting that one actual union from mu tensor lambda31 tensor lambda37 gives
one unnormalized measure nu11, supported outside every eleven-prime original,
with

    m(nu11)>=1+s-LQ=:m11
              =0.1689085230707447...>1/6.               (L4)

All old cofactor exponents, including the ternary exponent, are now arbitrary
in every original using31 or37. Their old projections were never inserted
as additional forbidden old originals. The source has changed only by
actual restriction of the one joint law.

## 4. All four-query products are bounded on that same measure

Use the existing geometric factor

    A4(p)=sum_(j>=1)((j+1)^4-j^4)p^-j
          =15t+50t^2+60t^3+24t^4,  t=1/(p-1).

For any four independently phased complete finite old query dictionaries,
expand their product into ordered numerical-label tuples. A compatible
intersection is one lcm cylinder; an incompatible intersection is empty.
The product source lambda has prefix caps C3=3/2 and Cq=(q-1)/(q-2) otherwise.
Since mu<=lambda/alpha*, the complete mixed fourth envelope is

    K9=(1/alpha*) product_(p in P9)[1+Cp A4(p)].

The same calculation with the two new pure-conditioned coordinates, followed
by the actual restriction already used in(L4), gives

    integral L1 L2 L3 L4 dnu11<=K11,
    K11=K9 product_(q=31,37)[1+Cq A4(q)]
       =112120806922512384639472776047817897341
         /15922408493425335546839040000000
       =7041698.93448....                               (L5)

No product structure is asserted for nu11, and these envelope maxima need
not be simultaneously attained. The mass and moment are unnormalized bounds
for the SAME physical source. Renormalizing after the mixed deletion would
change the interface and is not done.

## 5. Every finite tail strictly above1300 is affordable

Apply Report734 HM7--HM15 with

    k=4, delta=2/7, r=21, B=1300, ell=6.

Its growth comparison is verified coefficientwise:

    1+(7/5)A4(p)=1+21t+70t^2+84t^3+(168/5)t^4
                 <=(1+t)^21.

The analytic hypotheses B>=286, ell>=4,3^ell<=B and4ell>=21 hold. The
inherited Rosser--Schoenfeld prime-product estimate therefore gives total
tail loss at most K11*tau, where

    tau=(21609/10240)*(73/71)^21 *1300/1299^4
            *sum_(j=0..21)21!/((21-j)!18^j).

The exact rational comparison is

    m11-K11*tau=0.02686887323066282...>1/40.             (L6)

The theorem behind this finite constant assigns every original to its
greatest tail prime and keeps its entire earlier numerical cofactor and
globally fixed phase. It retains all finite exponent choices and any finite
number of tail primes. The actual conditional live kernels support avoidance
throughout. No intermediate prime below or equal to1300 is silently omitted.

The final mass is distorted measure mass. If desired, the initial source
has joint Haar cap

    D11=(3/2)product_(p=5,...,37)(p-1)/(p-2)/alpha*,

where the product runs over the ten listed nonternary head primes. With s
actual tail primes the final kernel cap is at most D11*(7/5)^s. Thus a valid
Haar-density lower bound is(5/7)^s/(40D11), not the undistorted number1/40.

## 6. Actual prime values, missing coordinates and the missing-three branch

Suppose3 is present in R. Pad R to eleven distinct odd primes at most1300
using primes absent from the actual family. Such padding adds no original
class. In the resulting ordered list, the first nine actual coordinates are
a subset of the originally specified R0: inserting dummy coordinates can
only increase an actual prime's position. Consequently every original wholly
on this padded first-nine head satisfies the required ternary cap. The last
two coordinates are allowed completely arbitrary ternary depths.

The padded list starts at3 and dominates the benchmark tuple3,5,...,37.
Keep the ternary coordinate literally fixed. At each of the other eight initial coordinates use
the existing [finite prefix-tree injections](../450-499/462-the-final-stage-ledger-gives-a-seven-core-common-law.md) from the benchmark prime to the
larger actual prime. Pull back ONLY old-head original classes. A pullback is
empty or one cylinder with the same complete exponent vector. Discard empty
classes; distinct original numerical labels stay distinct after replacing
the sorted actual prime vector by the benchmark vector.

For each finite injection choice choose its single normalized benchmark
source before examining any query. Push it forward and average over the
injections. This produces one supported actual probability. Every actual
complete query pulls back to a partial benchmark query, which may be completed
upward by nonnegative terms; the same holds for each product of four queries.
Therefore the uniform first and mixed fourth bounds survive each pushforward
and their average. The equal source mass1 is retained. The ternary map is
identity, so the higher ternary Haar suffix and(L2) are preserved. This does
not rename a different prime as3.

Finite injection heights may resolve the entire actual family's LCM,
including later cofactors. Higher unused digits are extended by independent
Haar; averaging extensions of the prefix injections gives that same law.
Thus later queries do not require a new query-dependent source. At the last
two small primes, actual primes are at least31 and37. Their pure caps and
geometric factors decrease with the prime, so(L4)--(L5) remain valid. Dummy
coordinates may be projected away after the construction.

If3 is absent from R, it is absent from the entire original support, since
3<1300. Use the existing empty-core pure-product construction directly on
eleven benchmark nonternary primes

    Pno3=(5,7,11,13,17,19,23,29,31,37,41).

With b_p=1/(p-2), one actual product of normalized pure survivors loses at
most sum_(|S|>=2)product_(p in S)b_p to the remaining mixed originals.
Its actual restricted measure has

    mno3>=2+sum_p b_p-product_p(1+b_p)
          =29127751/66621555=0.4372121155....

Its complete fourth envelope is

    Kno3=product_p[1+((p-1)/(p-2))A4(p)]
      =557206396227505564754974463643573027501307
        /19608473796830796549095424000000000000.

The same1300 tail gives mno3-Kno3*tau>1/40. Padding with nonternary dummy
primes and direct monotonicity handle at most eleven arbitrary actual small
primes. This argument has no ternary-height hypothesis at all. It uses the
same cutoff1300; a theorem assuming a support count through20000 would not
cover families with arbitrarily many primes between1300 and20000.

## 7. Verification and remaining scope

The [exact consumer](../../../frontier/cover-geometry/refined-capped-source/local_ternary_height_lift.py) and [retained result](../../../frontier/cover-geometry/refined-capped-source/local_ternary_height_lift.json) recompute
H0 from its complete mean and finite product atoms through8, then evaluates
every displayed response, quartic bound, pure-label subtraction and tail
inequality using exact rational arithmetic. Its proof premises remain
Report707's uniform source, the prefix transport and Report734's analytic
prime-product estimate. It does not claim to reprove these by decimal
arithmetic or rerun the full source's triangle comparison. Normal and
optimized Python both use explicit exception guards. Default execution
recomputes and compares the retained result; `--write-result PATH` emits a
fresh result after all checks pass.

The negative control with a depth-two ternary cylinder records why source
Haar suffixes cannot be omitted. The two-outside unit cost is checked
separately: pure conditioning excludes the singleton unit labels, but not
an original using both31 and37 with old cofactor1.

This connects an existing broad arbitrary-phase source to a larger valid
interface. It neither forces a coherent forbidden-root hypergraph in an
arbitrary phase layout nor proves Bfull<28 for unrestricted eight-prime
old heads. Families whose first-nine-only originals use deeper ternary
heights, or with more than eleven actual support primes at most1300,
remain outside this sufficient theorem. The unrestricted Erdős#7 goal is
unchanged.
