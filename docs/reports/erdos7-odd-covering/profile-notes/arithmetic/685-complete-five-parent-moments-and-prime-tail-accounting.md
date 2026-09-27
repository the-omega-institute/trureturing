# Complete five-parent moments and prime-only tail accounting

The retained-reference comparison of [Report684](684-retained-reference-blocks-tighten-five-parent-owner-fees.md) applies to the full seventh moment. Its canonical moment bounds all637 old noncanonical five-parent moments. Combining that complete branch bound with the actual prime owner set reduces the five-parent tail fee from approximately8.202932024191105e-7 to less than8.425632758019977e-8, retaining the actual half-row kernels, finite row parameters and all other continuation fees.

With684's finite fees, the fixed-four-start RS policy permits five parents from373 instead of397; the elementary policy permits five parents from443 instead of587. Prime-only accounting alone already reaches these two cutoffs with the old generic moment. The paired moment supplies additional reserve and a sharper reusable all-branch moment bound; it is not credited with cutoff changes that the scalar prime sum already provides.

These results remain conditional on678's actual matching source,684's enlarged-support measurable domination and the inherited ordinary-domain, private-coordinate and network assumptions. They do not remove head incidence restrictions or settle unrestricted Erdős #7. All proofs and rational checks here are ordinary mathematics, not new Lean verification.

Displayed decimal readings are rounded; every bound comparison and cutoff decision uses the exact rational endpoints in the certificates. Explicit decimal inequalities below are rounded in their stated safe direction.

## 1. A complete seventh moment on the same actual source

Use684's positive tau13 and its fixed actual references. Apply its retained-reference theorem to phi(t)=t^7, t>=0. This function is nonnegative, increasing and convex. Keep each original numerical modulus, owner height and globally fixed phase until after the source and coordinate comparisons. Distinct numerical moduli give the same full owner-height weight bound as684. Pure owner powers are already paid, so the completed count is

    C=X3 X5 (1+Y)(1+Z) X13-1>=0.

The canonical moment is

    Mpair=integral C^7 d(P3 product P5 product tau13 product P13).

The comparison measure has mass621424177961/986324169600, not one. Every positive geometric tail is included. Monotone convergence justifies completing a finite original family to all nonzero exponent patterns; no finite upper bound on the family's exponent heights is introduced.

For each other padded five-parent type(T,l), keep655's existing bound on the same actual source:

    Mold(T,l)=product_(q in Q minus T)Dq
              *E[(product_(p in T)Xp
                    product_(j=1)^l Xoutside,j-1)^7].

The ten head primes and ordered outside envelopes give638 types in total. For tail owners v>=1253, all five outside reference primes37,41,43,47,53 are earlier, so every type is eligible. The actual sorted outside parents u_j satisfy u_j>=r_j, and all earlier finite or half rows satisfy c_u/u<1/10. Consequently, on every complete preceding history,

    cylinder_mass(depth e)<=c_u/u^e
       <(1/10)u^(1-e)<=(1/10)r_j^(1-e).

Independent auxiliaries enter only after the lawful backwards comparison of actual kernels. No independence of the actual parents is assumed. Smaller parent sets are padded with zero-weight comparison roles before nonnegative completion, exactly as in684.

Exact evaluation of all638 moments gives

    Mstar=max(Mpair,max_(637 old noncanonical types)Mold)
          =Mpair
          =334087979992258328031675959229846798109333
             /167944130343158258073600000000.

The largest old noncanonical type is{3,5,7,11,17}. Every old noncanonical moment is strictly smaller than Mpair. This full-moment comparison is separate from684's finite hinge census: its exceptional owner41 hinge does not imply a moment exception.

## 2. Exact geometric moments, including the mass term

For X=L+1 with tail caps u(1)=kappa and u(e)=d*p^(-e) for e>=2, put q=1/p and

    S0=1/(1-q),
    Sk=q/(1-q)*sum_(j<k)binomial(k,j)Sj.

The tail identity gives mu0=1 and, for n>=1,

    mu_n=E X^n
      =1+(2^n-1)kappa
         +d*(sum_(j<n)binomial(n,j)Sj-1-q*(2^n-1)).

These are complete geometric sums, not truncated positive tails. With684's coefficients c00,c10,c01,c11, set

    A7(n)=mu7(n)-(1-1/6),
    A11(n)=mu11(n)-(1-1/10),
    pair_n=c00+c10*A7(n)+c01*A11(n)+c11*A7(n)*A11(n).

Then

    Mpair=sum_(n=0)^7(-1)^(7-n)binomial(7,n)
            mu3(n)mu5(n)mu13(n)pair_n.

In particular pair_0 is the mass of tau13. The constant term is minus that mass, not minus one. Signed binomial terms are evaluated as exact rationals. The independent implementation uses a different geometric-moment reconstruction and checks all638 exact values.

## 3. The inherited half row and the complete prime tail

At every actual five-parent tail owner keep the inherited N=0 relative half-threshold row with cap

    c_v=2(v-1)/(v-3).

It is defined and normalized on every complete preceding history, including wholly forbidden fibres. The scalar inequality

    (2x-1)_+<=A7*x^7, x>=0,
    A7=2^7*6^6/7^7,

follows by maximizing(2x-1)/x^7 on x>1/2; its maximum occurs at7/12. Applied to the same actual row and the complete moment bound, it gives the owner fee

    A7*Mstar/(v-3)^7.

The denominator remains(v-3)^7. The sharper finite-row ordinary-domain debit is not substituted into a different tail row.

Actual owners are primes. Enumerate all1025 primes1253<=v<10000, from1259 through9973, and write

    Sfinite=sum_(these primes v)(v-3)^(-7).

For the rest, every prime>=10000 is odd and lies among10001,10003,.... The decreasing function(x-3)^(-7), integrated over the length-two interval preceding each such odd integer, gives

    sum_(odd v>=10001)(v-3)^(-7)
       <=(1/2)integral_(9999)^infinity(x-3)^(-7)dx
       =1/[12*9996^6].

Therefore a complete scalar bound and tail fee are

    Sbound=Sfinite+1/[12*9996^6],
    W5_new=A7*Mstar*Sbound.                              (T1)

Numerically, Sfinite=5.840756515334334e-21... and the odd residual is8.353361363226901e-26.... Directed rational arithmetic bounds the expression W5_new by a narrow interval whose upper endpoint is8.425632758019976e-8.... This is an interval for the finite sum PLUS an upper remainder, not an enclosure of the unknown actual infinite prime fee from below. Its upper endpoint is the valid fee used in a lower reserve bound.

The old integer-padded tail fee was approximately8.202932024191105e-7. The improvement is approximately89.73 percent of that comparison fee and increases the projected reserve at every fixed finite schedule by at least1.7779664604218553e-8. The actual rows and source have not been changed.

Summing the owner-fee bound to infinity remains conservative for a policy that switches to arbitrary-parent rows at a finite later point. Only the five-parent part of the actual violation sum is bounded by the five-parent series. Extending that nonnegative series does not sample any additional actual row; the distinct arbitrary-parent violation bound is charged separately as before.

## 4. Complete paid schedules and attribution

Keep all193 finite h_v and caps,684's universal finite five-parent fees,683's four-parent fees, all326 Euler factors, the TypeI fee and both arbitrary-parent tail bounds. The RS and elementary final switches remain2^46 and2^68. The target is projected reserve>1/2000000, hence density>1/(2000000 Qoff) under the inherited projection.

| Complete policy | Three-parent rows | Four-parent rows | Five-parent finite rows | Projected reserve lower endpoint |
| --- | --- | --- | --- | ---: |
| RS |37..131|137..367|373..1249|5.037424188723978e-7|
| Elementary |37..181|191..439|443..1249|5.00953426842502e-7|

There are respectively21/41/131 and31/43/119 finite rows in these three ranges. The complete five-parent tail begins at1253; this boundary is composite, and its first actual owner prime is1259.

At the same fixed four-parent starts, the immediately preceding five-parent cutoffs367 and439 have upper reserves4.993623204186645e-7 and4.993253026189192e-7. They fail this fixed-schedule target. This is not a lower bound on every possible strategy or source.

The source of the numerical improvement is explicit:

| Tail comparison, using the same684 finite fees | RS five-parent start | Elementary five-parent start |
| --- | ---: | ---: |
| Inherited generic moment and all-integer tail |397|587|
| Paired all-branch moment and all-integer tail |389|509|
| Old generic moment and finite-prime tail |373|443|
| Old canonical all-branch moment and finite-prime tail |373|443|
| Paired all-branch moment and finite-prime tail |373|443|

Thus the paired moment improves the tail bound and reserve, but prime-only accounting already supplies the final cutoff change in this table. The old-generic prime-tail reserves at the same final cutoffs are5.031414131238514e-7 and5.003524210939555e-7; the new paired values are the larger reserves shown above.

Both policies are checked across all18915 ordered finite cutoff pairs. The result retains the complete undominated cutoff frontier and direct three-to-five schedules, with exact predecessor decisions. These conclusions concern the inherited row parameters and this family of schedules, not global optimization over new row kernels.

Further prime enumeration above10000 cannot by itself advance these two fixed-four-start cutoffs under this moment bound. Even setting the ENTIRE positive residual above10000 to zero leaves the preceding-cutoff upper reserves below the target:4.993623495266717e-7 and4.993253317269263e-7. This is a ceiling for further scalar-tail refinement at those fixed comparisons; a different moment or finite-row estimate is a separate question.

## 5. Verification and scope

The [producer](../../frontier/cover-geometry/paired_five_owner_prime_tail_certificate.py) and [result](../../frontier/cover-geometry/paired_five_owner_prime_tail_certificate.json) pin684,683, the inherited row schedule and657. They compute every complete coordinate moment and all638 branch moments exactly, sieve the finite prime window, bound every prime summand outwards at scale10^90, and pay the full analytic odd remainder. The reported tail interval has width below10^(-72). They verify154751 assertions, including both18915-pair policy decisions, attribution and the zero-residual ceilings.

The [independent verifier](../../frontier/cover-geometry/paired_five_owner_prime_tail_independent.py) and its [result](../../frontier/cover-geometry/paired_five_owner_prime_tail_independent.json) report117207 checks. It independently reconstructs all638 complete moments, identifies the1025 primes by trial division, compares their exact finite sum with the producer's directed term bounds, and verifies the odd residual, both18915-pair fingerprints, attribution and zero-residual ceilings. It neither imports nor executes the producer. The enormous exact common-denominator finite sum is only a transient verification value; the reusable result retains directed intervals and fingerprints.

Both canonical programs reproduce their result files byte for byte under isolated standard-library execution:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/paired_five_owner_prime_tail_certificate.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/paired_five_owner_prime_tail_independent.py
```

The ordinary proof above supplies the measure, label, all-height and infinite-tail obligations; finite computation alone supplies none of those semantic hypotheses. The exact diagnostic sources of681/682 are outside this source theorem unless their enlarged measurable domination is separately established. Head restrictions and unrestricted Erdős #7 remain unresolved.
