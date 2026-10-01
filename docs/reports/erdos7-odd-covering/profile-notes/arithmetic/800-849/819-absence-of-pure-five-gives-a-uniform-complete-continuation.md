# Absence of pure five gives a uniform complete continuation

For the actual opposing-phase family, excluding the numerical label 5 yields a positive certificate over the entire actual-pure source case. The fixed quarter table works with arbitrary finite higher pure 5 originals, arbitrary finite pure inventories at the other observed primes, the complete mixed and higher-ternary head inventory, and the full [Report 804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md) continuation.

The complete head mass floor is

    L_* = 29592789493376/374526636959475
        = 0.07901384460560555... .

With the same improved source cap used in every head, hinge and moment coefficient, the normalized continuation reserve is

    delta_* = 0.2967080519975316... > 29/100.

The key is an all-height source improvement: absence of the first pure 5 label gives C5=20/19 instead of 4/3. Merely restricting first-digit probabilities while leaving the old full-height charge unchanged would not establish this result. These are ordinary mathematical deductions with exact rational verification, not Lean results or unrestricted Erdős #7.

## 1. Restricted family and one source

Use the literal anchors 0 mod 3 and 1 mod 9 and the 23 selected actual originals of [Report 808](808-a-second-reference-colour-retains-an-actual-opposing-phase-continuation.md), including 10 mod15 and 11 mod 45. The23 selected (modulus, phase) pairs are

    (15,10),(21,7),(45,11),(33,22),(35,0),(39,13),
    (63,49),(51,34),(57,19),(55,0),(105,70),(75,25),
    (69,46),(65,0),(99,22),(77,0),(85,0),(117,13),
    (95,0),(165,55),(91,0),(147,49),(225,175).

All numerical moduli are odd, nonunit and globally distinct. The selected phases are fixed; no original is rephased by query or source region.

The old head is supported on {3} union Q, where

    Q=(5,7,11,13,17,19,23).

There is no original whose full numerical modulus is 5. This restriction does not remove moduli 25, 125, ... or mixed moduli divisible by5. Those higher pure 5 originals and all remaining head originals may have arbitrary fixed phases and arbitrary finite heights. The selected23 numerical slots remain fixed, and all other permissible mixed slots and higher ternary powers are included in the complete loss budget.

The continuation has the support and distinctness conditions of [Report 804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md): the 29-ending stage and any finite prime tail strictly above 1600. No result is asserted here for additional intermediate primes 31 through 1600. The complete prime-tail coefficient is

    T1600=4301685063112470380207/10^30.

For each q in Q, take Haar probability restricted to the actual pure-q survivor and normalize once. Their product is combined with the fixed ternary leaf weights

    w=(1/4,1/4,1/6,1/6,1/6)

on leaves (4,7,2,5,8), with roots {4,7} and {2,5,8}. Above ternary depth 2 use Haar. Thus r=1/2 and v=1/4. Higher pure ternary originals are charged in the complete higher-ternary loss; they are not silently assumed absent.

The retained table is the existing quarter table: retain every literal K8-allowed colour cell at its full leaf weight and set every selected-cylinder-forbidden cell to zero. There are 210 positive cells and 750 forced zeros. The categorical partition is {0},{1},{2,3,4} at 5 and {0}, nonzero at each other q. The retained measure is used to lower-bound the mass of the complete actual old survivor U. The normalized source for the hinge and full fourth moment remains

    mu = lambda_w restricted to U / alpha_actual,
    alpha_actual = lambda_w(U).

This report uses the full-source moment comparison, not [Report 815](815-retained-source-moments-have-a-three-point-common-kernel-obstruction.md)'s differently normalized retained-source moment.

## 2. A sharp all-height cap when the first pure label is absent

Fix a prime q>=3 and any finite set of actual pure originals modulo q^j with j>=2, at most one at each numerical label. Let S be their common survivor and H Haar probability. Overlaps are allowed. The deleted set is the actual union, so

    H(S)>=1-sum_(j>=2)q^-j
         =1-1/[q(q-1)].

For every cylinder J modulo q^e, e>=1, the same normalized survivor law obeys

    H(J intersect S)/H(S)
       <= q^-e/[1-1/(q(q-1))]
       = C_abs(q)/q^e,
    C_abs(q)=q(q-1)/(q^2-q-1).

One constant therefore controls every depth and every query cylinder simultaneously. It is not a cap obtained by separately choosing a pure family for each query. For finite families the complete deleted-budget bound is strict.

The uniform constant is sharp as a supremum. Protect root 0 and, for each finite E, delete

    1+q^(j-1) modq^j, j=2,...,E.

These cylinders are pairwise disjoint and lie in root 1. Their total deleted mass tends to 1/[q(q-1)], while every cylinder inside root 0 remains untouched. For any fixed depth and protected cylinder the ratio to its Haar mass tends to C_abs(q). No infinite original family is inserted into the finite theorem.

This reuses the actual-Haar deficit and finite-comb mechanism of [Report 542](../500-549/542-an-actual-sharp-nine-cell-interface-for-two-depth-stars.md) and the structural accounting of [Report 816](816-actual-pure-source-cells-and-a-finite-three-kernel-gap.md). The complete generic cap remains (q-1)/(q-2) when the label q is allowed. Consequently this case uses

    C5=20/19,
    Cq=(q-1)/(q-2) forq=7,11,13,17,19,23.

## 3. The source domain and every charge use those same caps

By the no-pure 5 case of [Report 816](816-actual-pure-source-cells-and-a-finite-three-kernel-gap.md), the observed 5-law belongs to

    conv{(3/19,4/19,12/19),
         (4/19,3/19,12/19),
         (4/19,4/19,11/19)}.

At every other q use the enclosing full interval 0<=piq(0)<=Cq/q. This allows arbitrary actual finite pure-q inventories. The source domain is one triangle times six intervals, with 3 times 2^6 = 192 product vertices. Exact finite attainment of its limiting vertices is not needed for an outer-domain upper/lower certificate.

The complete numerical inventory changes with the source cap:

    beta_D=product_(q inD) Cq/(q-1), beta_empty=1,
    R_Dh=initial_Dh-sum_(selected3^h n,supp(n)=D) C_D/n,
    C_D=product_(q inD) Cq.

Initial_D0=beta_D for |D|>=2; initial_D1 and initial_D2 equal beta_D for nonemptyD; all other shallow types are zero. Subtract each of the 23 selected numerical labels exactly once. The complete higher ternary debit is beta_D/2 on the leaf envelope, including D empty.

In particular the 5-axis inventory factor is 5/19, not 1/3. The common-colour envelopes and retained mass are evaluated at the same pi, with one common queried colour tuple whenever leaves or a root are summed. Thus

    L(pi)=M(pi)-sum_D R_D0 F_D0-sum_D R_D1 F_D1
                 -sum_D(R_D2+beta_D/2)F_D2

is a lower bound for alpha_actual. All coefficients are nonnegative.

The full hinge also uses the new caps at every depth. For the nonternary run factors Nq,

    Pr(Nq=1)=1-Cq/q,
    Pr(Nq=n)=Cq(q-1)/q^n for n>=2,
    E Nq=1+Cq/(q-1).

The complete infinite mean and exact subthreshold correction give H16(r,v). For the quarter weights,

    H16=0.26446535916509173... .

Finally, with A4(q)=15t+50t^2+60t^3+24t^4, t=1/(q-1),

    Kq=product_(q in Q)(1+Cq A4(q))
                        (1+(28/27)A4(29)),
    K29=Kq(1+15r+216v)
       =36327001785451748995687047881/83200263101987409100800.

The29 factor occurs exactly once. The full tail debit is

    27 K29 T1600=0.05071159043052277... .

No old 4/3 factor is retained in one layer while 20/19 is used in another.

## 4. One fixed table covers the entire case

For fixed u,w, the mass M is affine in each whole local probability block. Every F is a maximum of affine functions in that block, with a nonnegative coefficient in the loss. Hence L is block-concave. Its value throughout the product domain is at least its minimum over the 192 product vertices, all evaluated with the same quarter table.

Exact evaluation gives

    min L = L_*,
    min[12L-H16-27K29 T1600]
      =0.632989185671652... >63/100.

Both minima occur at pi5=(4/19,4/19,11/19) with every other zero-colour probability at its upper cap. All 192 vertex gates are positive. Therefore

    alpha_actual>=L(pi)>=L_*>0

for every actual source in the stated no-pure 5 class, with arbitrary finite old pure heights and remaining mixed phases.

Let charge=H16+27K29 T1600>=0. [Report 804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md)'s normalized continuation reserve is bounded below by

    12/27-charge/(27alpha_actual)
       >=12/27-charge/(27L_*)
       =delta_*> 29/100.

This uses a valid lower bound for the same source denominator and a constant nonnegative charge valid for that source. It does not combine separately optimized sources or substitute an unrelated normalization. The resulting process is supported on the actual survivors and has positive mass, so every finite family in this restricted class leaves an integer uncovered.

The unchanged point 812 table was also evaluated once on this domain as a comparison. It passes all 192 vertices, with minimum gate 0.5707337961090235... and corresponding uniform reserve 0.2887983234026467.... The quarter table alone supplies the theorem; no pointwise choice between tables is required.

## 5. Boundary and verification

This is a whole structural source case, not a sampled source point, but it retains the literal selected-phase family and the specified head/tail support. It does not cover a present pure 5 original, arbitrary selected phases, arbitrary intermediate prime support, or unrestricted Erdős #7.

The exact consumer reconstructs the literal selected-cylinder zeros, both unchanged tables, the complete new-cap inventories, full infinite-law hinge and fourth moment, and the full [Report 804](804-the-same23-label-source-admits-every-finite-prime-tail-above1600.md) tail. It evaluates exactly the 192 specified vertices for each table. No solver, added cuts or repeated parameter tuning is needed.


The [standalone exact consumer](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/no_pure_five_uniform_continuation.py), [certificate](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/no_pure_five_uniform_continuation_certificate.json), and [generated result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/no_pure_five_uniform_continuation.json) contain the complete reproducible data.

```sh
python3 -I -S -B no_pure_five_uniform_continuation.py
```

Normal execution verifies the saved result without rewriting it. Regeneration uses --write-result; alternate paths use --certificate and --result. The 2295 exact checks include the arbitrary-height absence-cap arithmetic, literal quarter table, every new-cap coefficient, the complete 179-prime bridge to the analytic tail above 3000, all specified source vertices, and the strict normalized 29/100 reserve. Floating numbers are displays only.
