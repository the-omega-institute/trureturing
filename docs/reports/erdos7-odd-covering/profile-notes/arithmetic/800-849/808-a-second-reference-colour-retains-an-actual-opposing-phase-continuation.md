# A second reference colour retains an actual opposing-phase continuation

A binary first-digit summary at5 cannot represent the retained core needed
by the actual originals10 mod15 and11 mod45. Keeping the three categories
0,1,and every other digit makes that core explicit. On the same fixed
five-leaf source, the complete residual inventory then admits arbitrary29
originals and every finite prime tail strictly above1600, with distorted
survivor mass greater than49/1000.

This sufficient result requires empty old pure-q inventories for
Q=(5,7,11,13,17,19,23), the23 stated selected phases, and the complete
common-source construction below. The support is contained in

    {3,5,7,11,13,17,19,23,29} union {p prime: p>1600}.

Primes31 through1600 remain excluded. All unlisted mixed head phases,
higher ternary heights,29 phases, and permitted larger-prime phases and
heights are arbitrary and finite. Original numerical moduli remain odd,
greater than1 and pairwise distinct. This is ordinary mathematics and exact
rational verification, not Lean verification or unrestricted Erdős#7.

## 1. One changed original requires one more observable category

Take the actual25-original family in
[Report803](803-common-reference-phases-and-five-leaf-weights-do-not-remove-the-phase-obstruction.md),
changing only its modulus45 original from40 mod45 to11 mod45. In particular,

    10 mod15 has ternary root1 and5-digit0;
    11 mod45 has ternary leaf2 mod9 and5-digit1.

The pure anchors remain0 mod3 and1 mod9. Use the live leaves(4,7,2,5,8)
and the one fixed law

    w=(1/4,1/4,1/6,1/6,1/6),

with Haar suffixes above ternary depth2. At each nonternary prime use its
actual normalized pure-power survivor law. No actual original is rephased
individually. The selected inventory is

    15,21,45,33,35,39,63,51,57,55,105,75,
    69,65,99,77,85,117,95,165,91,147,225.

Write E_q={x_q=0 modq}. In addition to these zero-hit indicators, retain
F_5={x_5=1 mod5}. Their probabilities on one product source are

    t_q=lambda_q(E_q), u=lambda_5(F_5).

At5 the probabilities are categorical:

    P(0)=t_5, P(1)=u, P(other)=1-t_5-u.                 (SC1)

The events E_5 and F_5 are mutually exclusive. They are not independent
Bernoulli coordinates. Coordinate independence is used only between
DIFFERENT primes.

Define the actual retained core by

    leaves4,7: no zero-hit at any q;
    leaves5,8: at most one zero-hit;
    leaf2: at most one zero-hit, and x_5 !=1 mod5.       (SC2)

Every selected no3 original has at least two distinct zero-hit primes and
is excluded. Every selected ternary original other than45 meets the short
root and requires a zero-hit there. The changed45 original meets leaf2
and requires F_5, so it too is excluded. Thus all23 selected actual
cylinders are pointwise disjoint from this ONE core. This remains a set
statement under any actual pure-power law, even though the successful
continuation below specifically uses empty old pure-q inventories.

The earlier leaf-dependent core of
[Report806](806-actual-ternary-leaf-cores-give-a-finite-common-source-linear-program.md)
handled20 mod45, which has5-digit0. Changing that digit to1 is an actual
change to the common family. It is not a permitted relabelling of45 alone
while keeping the other actual5 phases fixed.

## 2. A common safe replacement gives valid intersection bounds

For a queried supportD subsetQ, replace its5 coordinate, if present, by
a digit in{2,3,4}; replace every other queried coordinate by a nonzero
digit. The representative choices x_5=2 and x_q=1 forq!=5 suffice.
This operation simultaneously enlarges every core inSC2. It removes zero
hits and, at5, also removes the excluded1 colour. In particular, the
maximizing assignment is common to all leaves; no mutually incompatible
per-leaf maxima are combined.

Let A_D and B_D be the probabilities of zero and at most one zero-hit,
respectively, among primes inQ\({5} unionD). Equivalently,

    A_D=product_(q in Q\({5} unionD))(1-t_q),
    B_D=A_D+sum_q t_q product_(r!=q, r in Q\({5} unionD))(1-t_r).

If5 belongs toD, the five response probabilities after this common safe
replacement are

    (A_D,A_D,B_D,B_D,B_D).                             (SC3)

If5 does not belong toD, they are

    ((1-t_5)A_D, (1-t_5)A_D,
     (1-t_5-u)B_D+t_5 A_D,
     (1-t_5)B_D+t_5 A_D,
     (1-t_5)B_D+t_5 A_D).                              (SC4)

The middle expression uses all three probabilities inSC1. Dropping the
term involvingu would reinstate a positive selected45 intersection.

Put a_(l,D) for these responses. With C_q=(q-1)/(q-2), define

    F_(D,0)=sum_l w_l a_(l,D),
    F_(D,1)=max(w4 a_(4,D)+w7 a_(7,D),
                w2 a_(2,D)+w5 a_(5,D)+w8 a_(8,D)),
    F_(D,2)=max_l w_l a_(l,D).                          (SC5)

For an actual cylinder of numerical modulus3^j n, supp(n)=D, its
intersection with this core has mass at most

    (C_D/n) F_(D,j), j=0,1,2;
    (C_D/n) 3^(2-j) F_(D,2), j>=3.                     (SC6)

Indeed its queried coordinates fix one literal colour assignment. The
common safe replacement enlarges its permitted outside-coordinate event;
independence across primes and the original cap C_q/q^e bound the queried
cylinder. Its actual ternary phase chooses all leaves, one root, one leaf,
or a deeper Haar descendant as appropriate. This proof never treats a
query's phase as an extra source choice.

## 3. Full inventories and the256-vertex boundary

Retain the complete support inventories

    beta_D=product_(q inD)1/(q-2), beta_empty=1.

Subtract the23 selected numerical slots once each, exactly as in
Reports801 and806, obtaining nonnegative R_(D,j) forj=0,1,2. Height0
uses only|D|>=2, and heights1,2 use nonemptyD; the other shallowR values
are zero. Every heightj>=3, including pure3 powers, is retained by
sum_(j>=3)3^(2-j)=1/2.

IfU is the complete actual old survivor andG is the coreSC2, then

    lambda(U)>=lambda(U intersectG)>=L(t,u),
    L=F_(empty,0)-(1/2)sum_D beta_D F_(D,2)
                         -sum_(D,j=0,1,2)R_(D,j)F_(D,j).       (SC7)

These are conservative charges insideG, with all unlisted numerical
labels and exponent tails included. A selected numerical slot may also
be absent from the actual family: it then has zero actual deletion, just
as a present core-null slot does, so subtracting that inventory slot is
still valid. Any later insertion at that selected numerical slot must
still satisfy the same actual core-null contract. The displayed
certificate includes all25 originals. Intersections between removed classes
are allowed; no disjointness between those removed classes is assumed.

For arbitrary actual pure-q inventories, the original caps give

    0<=t_q<=C_q/q, 0<=u<=4/15.

At5, t_5<=4/15 also. Thus every point in this rectangular relaxation
satisfies t_5+u<=8/15<1, soSC1 is a valid categorical probability vector
throughout. A finite actual pure family need not attain the endpoints.

Each response inSC3–SC4 is affine in each individual coordinate of(t,u).
InSC7 the maxima have nonnegative loss coefficients. Therefore L is
separately concave in the EIGHT variables and

    L(t,u)>=min_(epsilon in{0,1}^8)L(at the corresponding endpoints).
                                                               (SC8)

This gives256 vertices, replacing the128 of the old binary interface.
It does not assert independence of E_5 andF_5; it uses the joint categorical
formulaSC4 before varying its two probability parameters.

For the declared quarter-law, the256-vertex minimum is

    -1393835409216139/248370296088915000,

at the all-upper vertex. It is negative. Thus this particular uniform
certificate does not supply a positive source for arbitrary pure-q
inventories. This is a failure of the specified bound, not an actual
covering example or a proof that finer sources cannot work.

Under EMPTY old pure-q inventories, the actual vector is instead

    t_q=1/q, u=1/5.

Retaining the same looser C_q constants in every remaining charge gives

    alpha=7537807164539/215039217393000>0.              (SC9)

This is a lower bound, not the actual survivor mass. The corresponding
core, high-ternary and remaining shallow charges are

    core=2187552/3380195,
    high=409641162096457/2365431391323000,
    shallow=1736242534693/3955570888500.

Their signed difference isSC9. The program also directly verifies the
common phase-null conditions and the common safe replacement on every
leaf, literal5 digit, remaining hit pattern and queried support.

## 4. The same full source continues through29 and every prime above1600

Use the normalized restriction mu=lambda|U/lambda(U) to the complete old
survivor, with lambda(U)>=alpha. The original full product law supplies
both its complete-query hinge and its complete mixed fourth moment,
as inReport805. This paragraph does not use the core-restricted fourth
moment fromReport807.

At the ONE fixed thresholdh=16, the full-height comparator gives

    B(mu)<=16+H16/alpha=24.87924699954... .              (SC10)

The unit numerical query remains included. H16 uses the complete mean
plus exactly the atoms below16, so no upper exponent tail is truncated.
The original source has root cap1/2 and leaf cap1/4. After the actual
pure29 survivor factor, its unnormalized fourth-product numerator is

    K29=(1+15/2+216/4) product_q[1+C_q A4(q)]
                         [1+(28/27)A4(29)]
       =7101326389957751920822379861/13136883647682222489600.

Avoiding all remaining29-ending originals gives mass at least
(28-B(mu))/27. Its mixed fourth moments are bounded byK29/alpha on that
same unnormalized source.

Use the source-independent transfer from
[Report804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md):

    T1600=4301685063112470380207/10^30.                 (SC11)

Starting with its full analytic>3000 allowance, include every one of the
179 primes1601,...,2999, in decreasing order, by

    Phi_p(T)=64827/[10240(p-1)^4]+[1+(7/5)A4(p)]T.

Every step is rounded UP to the1/10^30 grid. Phi_p is increasing and
dominates the identity, so the complete interval bounds every subset of
these primes. The complete analytic tail retains all later primes and
heights. The consumer rebuilds the entire prime interval and all179
updates; it does not acceptSC11 as an unverified input number. The
Rosser–Schoenfeld analytic premise remains the inherited one ofReport734.

The final supported distorted mass consequently satisfies

    mass >= (28-B(mu))/27-(K29/alpha)T1600
         >= (28-16-H16/alpha)/27-(K29/alpha)T1600
          =0.04924605453919601...>49/1000.             (SC12)

Positive supported mass gives an actual common finite CRT survivor.
Every finite extension meeting the stated selected-phase, source and
prime-support conditions therefore remains noncovering. The mass floor
is not a Haar-density claim of the same size.

As a control, directly applying the larger analytic allowance at1600
withell6 gives approximately-0.05116864641638629. That negative estimate
does not contradictSC12, which uses the179-prime bridge followed by the
analytic>3000 tail. Neither conclusion can replace the source premise
ofSC9 by the failed256-vertex bound.

## 5. Why the added colour is genuine retained information

On ternary leaf2 with all other zero-hit indicators absent, x_5=1 and
x_5=2 both have the old binary readout1_(x_5=0)=0. The first is rejected
bySC2, while the second is accepted. Hence that particular binary summary
cannot reconstruct membership in the stated core.

These differences occur in the same full resolving period11712375675:

    2602750151 has leaf2 and5-digit1; it hits the changed45 original;
    8693185502 has leaf2 and5-digit2; it avoids all25 originals.

Both have the same old zero-hit pattern. The consumer checks its declared
positive CRT witness against the entire actual family. The examples show
why phases must stay tied to their original numerical labels and common
source.

There is also a probability-law distinction with the same old readout.
At5, compare the actual pure survivor obtained by removing1 mod25 with
that obtained by removing2 mod25. Both have t_5=5/24, but their phase1
probabilities are respectively

    u=1/6 and u=5/24.                                   (SC13)

Thus the old t vector does not determineSC4. These nonempty pure
inventories are counterexamples to the old information interface; they
are not silently inserted into the empty-pure positive theorem.

More colours or deeper prefixes may require a larger interface again.
This construction establishes only the extra distinction needed here.
It does not claim a universally finite state budget independent of all
actual phases and exponents.

## 6. Exact evidence and the remaining scope

The [consumer](../../../frontier/cover-geometry/refined-capped-source/second_reference_colour.py),
[certificate](../../../frontier/cover-geometry/refined-capped-source/second_reference_colour_certificate.json)
and [result](../../../frontier/cover-geometry/refined-capped-source/second_reference_colour.json)
retain the literal family, fixed weights, all256 source controls,
complete query and moment data, and every rounded prime-transfer step.
The consumer uses only standard-library arithmetic and explicit adjacent
inputs. To reproduce:

```sh
python3 -I -S -B second_reference_colour.py
python3 -I -S -B -O second_reference_colour.py
```

`--certificate` and `--result` accept explicit paths, while
`--write-result <path>` regenerates the exact result. All decisions use
explicit checks that remain active under optimized Python. Ordinary,
optimized and relocated execution with spaces in the path agree;
twelve altered certificate/result kinds are rejected in both modes. A
positive control removes the actual15 original while retaining its
selected inventory slot; its bound remains valid because that absent
slot also contributes no actual deletion.

The independently written source calculation agrees on the actual Haar
fraction, all256 endpoint components, the full hinge and both different
tail coefficients. The general conditional statement is supported by
SC1–SC12 and the cited full-tail theorem, not by a claim that a finite
search settled all original families. Arbitrary shallow phases, arbitrary
old pure-q inventories and the unrestricted intermediate prime support
remain unresolved.
