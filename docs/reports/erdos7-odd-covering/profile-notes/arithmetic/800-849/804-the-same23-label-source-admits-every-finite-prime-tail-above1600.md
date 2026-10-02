# The same 23-label source admits every finite prime tail above 1600

Under the 23-label phase-null contract of [Report801](801-retained-core-intersections-reduce-shallow-phase-contracts-to23-labels.md), the same fixed source admits every finite set of additional primes strictly above 1600, with all original heights and phases unrestricted outside that contract. Its final distorted mass is greater than 9/1000. This replaces Report801's cutoff 3000 by 1600 without changing its source, selected labels, query law, or fourth-moment initialization.

The new step is an exact finite-prime bridge between that source and Report734's complete analytic tail. It uses every one of the 179 primes in (1600,3000], not a selected sparse subsequence. Positivity of the transfer gives domination of arbitrary subsets. No enumeration endpoint is imposed on the primes above 3000.

This is an ordinary conditional proof with exact rational verification, not new Lean verification or a solution of unrestricted Erdős #7. The support remains contained in {3,5,7,11,13,17,19,23,29} together with a finite set of primes strictly above 1600. Primes 31 through 1600 remain excluded. The same actual phase-null contract and inherited Rosser–Schoenfeld analytic premise remain required.

## 1. Precisely the same source

Let Q=(5,7,11,13,17,19,23). Normalize the pure 3/9 originals by the one common map of Report801. Keep its fixed ternary weights

    (3/16,3/16,5/24,5/24,5/24)

on leaves (4,7,2,5,8), with Haar suffixes, and its actual pure-q survivor law on each q in Q. Let lambda be this one product law and G its reference core: no pair of q-hit events may occur; on ternary root 1 the 5-hit is excluded; on root 2 every non5 hit is excluded. All mixed actual phases are transported by that same normalization.

The selected numerical labels are exactly

    15,21,45,33,35,39,63,51,57,55,105,75,
    69,65,99,77,85,117,95,165,91,147,225.

For each selected label that is present, require

    lambda(G intersect actual_original_m)=0.                 (FP1)

Absent selected labels are free. The reference exclusions are not asserted to be additional original congruence classes. Every original label remains odd, greater than 1, and numerically distinct; all nonselected shallow phases and all higher ternary heights are arbitrary.

Report801 RC1–RC11 gives the source bound

    alpha=16790988780569/557509082130000,

and the complete query bound B*=16+E(Z-16)_+/alpha. Here the fixed auxiliary run comparison has

    Pr(J3>=1)=5/8,
    Pr(J3>=e)=(5/24)3^(2-e), e>=2,
    Pr(Jq>=e)=((q-1)/(q-2))q^(-e), e>=1,
    Z=product_(p in {3} union Q)(1+Jp).

These independent comparison runs bound complete queries; they do not replace the actual source. The exact hinge includes the full mean and the finite correction below 16, so no actual exponent is truncated.

Use the actual pure29 survivor law and restrict to every remaining actual29 survivor, exactly as in Report801 RC12. The resulting one positive submeasure nu29 has absolute mass at least

    m=(28-B*)/27=approximately 0.07781905857165276.        (FP2)

For every four complete actual queries on the full old exponent carrier, the same measure satisfies

    integral Q1 Q2 Q3 Q4 dnu29 <= K,
    K=303820385851986764614967500067258071
       /19105587337954450838679060480
     =approximately 15902174.608808203.                    (FP3)

More explicitly, with Cq=(q-1)/(q-2), r=5/8 and v=5/24,

    K=[1+15r+216v] product_(q in Q)[1+Cq A4(q)]
           *[1+(28/27)A4(29)]/alpha,
    A4(p)=15t+50t^2+60t^3+24t^4, t=1/(p-1).

This K is Report801's fourth_product_with29 divided by its alpha, not a newly normalized law or a separately optimized source. The old coordinate heights include cofactors that occur only in later originals. Such cofactors are query labels, not additional forbidden originals.

## 2. One actual transfer and its positive affine budget

Expose actual outside primes in increasing order and assign each remaining original once to its last outside prime. Keep its full earlier cofactor, actual phase, and exponent. At the next prime p, [Report734 HM7–HM12](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md) uses its actual forbidden fibre Bx and beta(x)=Hp(Bx):

    Rx(dy)=1_(y notin Bx) Hp(dy)/[1-min(beta(x),delta)].

For delta=2/7 its row mass is at most 1. No global probability renormalization occurs. If the current common measure has a complete fourth-query bound Kcurrent, its absolute loss and next complete fourth-query bound satisfy

    loss_p <= Kcurrent c(p),
    Knext <= Kcurrent g(p),
    c(p)=C/(p-1)^4,
    C=27/[256 delta^3(1-delta)]=64827/10240,
    g(p)=1+A4(p)/(1-delta).                               (FP4)

The complete query used to bound the activation load may exceed 1; it is not substituted for beta in the actual row denominator. The moment calculation and transfer both act on the same current measure. Finite actual heights are bounded by the complete convergent exponent sums in A4; they are not assumed to be 1 or 2.

Suppose the total subsequent loss is at most Knext T. Then the loss starting before this prime is at most

    Kcurrent Phi_p(T),
    Phi_p(T)=c(p)+g(p)T.                                 (FP5)

For T>=0, this map is increasing and Phi_p(T)>=T because c(p)>0 and g(p)>=1. Omitting a prime replaces Phi_p by the identity, which is pointwise smaller. A composition of increasing maps preserves this inequality. Thus the budget for the complete interval dominates the budget for every one of its prime subsets, without assuming that every prime actually occurs.

## 3. The full analytic tail still starts at 3000

At delta=2/7 the growth polynomial is

    g(p)=1+21t+70t^2+84t^3+(168/5)t^4 <= (1+t)^21

for t>=0, by coefficient comparison. Set B=3000, ell=7 and growth exponent r=21. Report734 HM14–HM15 applies: B>=286, ell>=4, 3^ell=2187<=3000 and 4ell=28>=21.

Its inherited Rosser–Schoenfeld prime-product premise yields the complete allowance

    tau3000=(C/3)(99/97)^21 * 3000/2999^4
                *sum_(j=0..21)21!/[(21-j)!21^j]
      =2862135126203448853479566306418262887219011176150637659519425
       /3704203284387292255616197333120609401644382873987910812398103977158784.
                                                               (FP6)

For any finite actual prime subset above 3000 and the current measure with fourth-query bound Kcurrent, all subsequent loss is at most Kcurrent tau3000. This is the same tau3000 already used in Report801. Its proof majorizes by the complete prime-product bound and a convergent all-integer integral. No primes beyond 3000 are enumerated or silently omitted.

## 4. A complete finite-prime bridge and a strict margin

List every prime in the interval as

    1601=p1<p2<...<p179=2999.

Begin with T180=tau3000 and recurse backwards, for i=179,...,1:

    Ti=ceil(10^30 [c(pi)+g(pi) T_(i+1)])/10^30.          (FP7)

Every step rounds upward. The difference between the rounded and unrounded value at that step is nonnegative and strictly less than 10^(-30). Since each Phi is increasing, induction proves that T1 dominates the exact complete-interval loss coefficient including the analytic tail. The omitted-prime argument from FP5 proves the same domination for every actual subset.

The retained exact value is

    T1=4301685063112470380207/10^30.                    (FP8)

As a separate arithmetic consistency check, forward accumulation gives

    T_exact=sum_(i=1..179)c(pi) product_(j<i)g(pj)
                  +tau3000 product_(i=1..179)g(pi).

The exact consumer verifies this identity against its unrounded backwards recursion, checks every rounded suffix dominates its exact suffix, and obtains

    0<=T1-T_exact<10^(-26)

(approximately 2.428707866350145 times 10^(-28)). The initial analytic tau is retained exactly; it is not rounded downward.

The final same-source absolute mass is therefore at least

    R=m-K T1
     =approximately 0.009412911585936127
     >9/1000.                                           (FP9)

The strict inequality and its exact rational excess are retained in the result below.

Positive supported mass on the full finite CRT carrier supplies an actual surviving residue and hence an uncovered integer. The number 9/1000 is a lower bound for this distorted measure, not a Haar-density lower bound of that size.

## 5. Two bounded cutoff controls

The consumer also checks two specified neighboring extensions, with the same source, delta, analytic tail, and upward rounding. Including all 188 primes from 1543 through 2999 gives a reserve approximately 0.0005189969616391703, greater than 1/2000. Adding the next prime 1531 gives a reserve approximately -0.0005626691862663972.

The negative number is failure of this fixed scalar certificate. It is neither an actual covering family nor an impossibility theorem for smaller cutoffs, different parameters or stronger estimates. No global parameter optimization is asserted. The simple cutoff 1600 is the main statement.

## 6. Reproducibility and remaining scope

The [standalone consumer](../../../frontier/cover-geometry/refined-capped-source/retained_core_prime_bridge.py) takes explicit paths to the [Report801 source result](../../../frontier/cover-geometry/refined-capped-source/retained_core_phase_union.json), the [bridge certificate](../../../frontier/cover-geometry/refined-capped-source/retained_core_prime_bridge_certificate.json), and the [retained exact result](../../../frontier/cover-geometry/refined-capped-source/retained_core_prime_bridge.json). It uses only the standard library. The source binding is

    SHA256 dc4ceba98c8e992a85c001d50aed1928a255c937f4b1bc248b6f1850cb6e222c.

In addition to this version binding, the program reconstructs the selected original-label inventory, all 128 source vertices, the full query hinges, the post29 absolute mass and the fourth-query bound. It does not merely trust copied decimal fields. It checks the target source case; the other two laws and the source report's minimality claims are outside this bridge's replay scope.

The 1400 integers from 1601 to 3000 are independently classified by a sieve and trial division through each integer's square root. Exactly 179 are prime and the other 1221 are composite; the certificate's entire ordered prime list must agree. Every continuation row retains its exact cost, growth, incoming allowance, outgoing allowance, and rounding slack. Duplicate JSON keys are rejected.

The main calculation completes 3754 explicit checks. Normal and optimized execution both succeed after copying all four files to a directory with spaces and using unrelated input filenames. Nineteen forged inputs are rejected in each mode, including missing and composite prime entries, incorrect ordering, changed cutoff or rounding scale, altered output rows, duplicate keys, and modified source masses, quartics, vertices, labels or analytic tails even after rebinding their source hash. These checks support the arithmetic implementation; they do not discharge FP1 for an arbitrary covering candidate or formalize the analytic premise.

Example after installation beside the existing source result:

```sh
python3 -I -S -B retained_core_prime_bridge.py \
  --source retained_core_phase_union.json \
  --certificate retained_core_prime_bridge_certificate.json \
  --result retained_core_prime_bridge.json
python3 -I -S -B -O retained_core_prime_bridge.py \
  --source retained_core_phase_union.json \
  --certificate retained_core_prime_bridge_certificate.json \
  --result retained_core_prime_bridge.json
```

Use --write-result instead of --result to regenerate the exact output. No default working directory or repository import is required.

The advance is the inclusion of every intermediate prime from 1601 through 3000 under the existing 23-label source contract. The original-label contract and the still-excluded primes from 31 through 1600 remain the gaps to an unrestricted conclusion. No result for a changed phase contract is imported into this smaller tail allowance without a new common-source check.
