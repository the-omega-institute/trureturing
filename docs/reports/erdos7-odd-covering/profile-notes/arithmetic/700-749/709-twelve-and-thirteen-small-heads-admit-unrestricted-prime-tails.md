# Twelve and thirteen small heads admit unrestricted large-prime tails

The density bounds in [Report707](707-shared-support-avoidance-closes-twelve-height-one-primes.md)
and [Report708](708-a-shared-support-sign-bridge-closes-thirteen-height-one-primes.md)
combine directly with [Chapter33 SH13](../../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md).
This gives two noncoverage conditions for a finite family of distinct
odd nonunit numerical moduli:

| Bound B on the small primes | Maximum number of actual support primes <=B | Height condition |
| --- | ---: | --- |
| 100000 | 12 | v3(m)<=1 only for originals supported entirely on the small primes |
| 1000000 | 13 | v3(m)<=1 only for originals supported entirely on the small primes |

Originals touching a prime greater than B may have arbitrary finite
exponents, including deeper ternary heights. There is no uniform bound
on the number of tail primes. Each of the two conditions implies an
uncovered integer. This is an ordinary application of an existing tail
theorem with exact rational constants, not new Lean verification.

## The source is changed explicitly at the full required height

Let R contain all actual support primes <=B and let U avoid exactly the
head-only originals. Resolve the head coordinates at the heights required
by the ENTIRE original family, including tail-touching originals. Uniform
lifting preserves U's Haar mass. Use the submeasure

    eta=H_R restricted to U, eta<=H_R.

The two source results, including their separate no3 branches, give
eta(1)>m for m=1/450 and m=1/11000 respectively. This source change
requires no preservation of the earlier restricted query norm. SH6
supplies the all-depth joint Haar moment for every later head cofactor:

    M2(R)<=product_(p in benchmark head) p(p+1)/(p-1)^2.

These factors decrease with p and exceed one, so the first twelve or
thirteen odd primes give the respective bounds for any allowed actual
head, including a smaller head or one not containing3.

## The complete tail charge is smaller than the head reserve

Use SH11--SH13 with D=1. For cutoff B and integer ell define

    c_ell=(2ell^2+1)/(2ell^2-1),
    P_7(ell)=sum_(j=0..7) 7!/((7-j)!ell^j),
    tau7=c_ell^7 B/(B-3)^2 P_7(ell).

The inherited analytic premises are B>=286, ell>=4 and3^ell<=B,
together with SH11's prime-product estimate and its Rosser--Schoenfeld /
Chapter32 source attribution. The exact rational checker verifies the
displayed substitutions; it does not reprove the analytic estimate.

For the twelve-prime head, set B=100000 and ell=10. Then

    M2<=17517439415203/525533184000,
    c_ell=201/199, P_7=305593/125000,
    tau7=16202267391964665023172/617896138521372358365262955.

The one final distorted law retains mass greater than

    1/450-M2 tau7
      =3742935494226044967324160844981
       /2776280950193579798410499604480000
      =.0013481832571610103... >1/750.                 (ST1)

For the thirteen-prime head, set B=1000000 and ell=12;3^12=531441<=B.
Here

    M2<=107607127836247/3009871872000,
    c_ell=289/287, P_7=509855/248832,
    tau7=1341379324381927510238984375
         /623586820236187800483190891161936.

The one final distorted law retains mass greater than

    1/11000-M2 tau7
      =7052553394792933937889538512289220863837
       /503562944628464454366413341299126102392832000
      =.000014005306526270323... >1/100000.             (ST2)

These are distorted-measure mass bounds, not full-family Haar or natural
density bounds of1/750 or1/100000. Their positivity supplies an actual
uncovered configuration in the complete finite CRT period and hence an
uncovered integer.

SH13's normalized kernels preserve the whole preceding measure. Every
original is charged once at its last tail prime, with its original
phase and all earlier exponents retained. All bad sets are deleted from
the same final law. Thus the source, head moments and tail losses belong
to one common construction; independently optimized branches are not
combined.

## Verification

The [portable checker](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_support_tail.py)
pins both head-density certificates and verifies both the with3 and no3
mass premises. It recomputes only the two new SH6/SH12 substitutions,
not the source geometry or the query calculations. Its [result](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_support_tail.json)
retains the exact moments, analytic parameters, losses and positive
reserves. Default replay compares the retained result, and explicit
output mode regenerates it. Independent factor and polynomial
calculations agree with both cases. Normal, optimized and
different-directory execution agree; modified seed/result controls are
rejected. Only standard-library exact arithmetic is required.

Larger small-prime supports and arbitrary ternary heights among
head-only originals remain outside these sufficient conditions.
