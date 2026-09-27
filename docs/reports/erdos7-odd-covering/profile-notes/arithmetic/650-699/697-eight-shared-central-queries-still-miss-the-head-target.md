# Eight shared shallow central queries still miss the head target

The fixed actual109 source cannot reach193/100000 through the complete shallow central query block

    D={3,5,9,15,25,45,75,225}.

Keep one independent residue for each numerical label, reused in every factor containing that label. Retain all original-loss charges, all other query factors, the full-height coefficients and the four fullmode8 additions. A feasible rational dual gives

    U8=25577252076591987554787560844798176215702649
       /13481659352694140862533959680000000000000000000
      =0.0018971887219120913... <193/100000.

This bounds every joint measurable retention field on the fixed source, including dependence on arbitrarily deep digits. It strengthens the scope of the triangle obstruction in [Report696](696-the-shared-triangle-gate-still-misses-the-target.md) to the complete eight-label block. The new bound is also valid below target for the stated joint central density-cap extension with the outside reference fixed. It does not exclude larger blocks involving outside primes, arbitrary reference sources, changed original phases or unrestricted Erdős#7. The argument and exact finite checks are not new Lean verification.

## The changed objective and exact factor ownership

For a finite positive retained measure nu=f sigma, define

    I_d(x)=1_(x=b_d mod d),
    n_b=sum_(d in D) I_d,
    K8(nu)=max_(b_d mod d, d in D) integral (n_b^2+2n_b) dnu.

The eight choices are independent. They need not come from one common residue modulo225. The same complete layout is used at every source point. Since all nonunit divisors of225 occur, the selected square factors are exactly eight unaries with coefficient3 and28 unordered pairs with coefficient2. Grouping their independent bounds by lcm gives

    B8(nu)=3q3+3q5+5q9+9q15+5q25+15q45+15q75+25q225,
    qd=max_r nu([r]_d),
    K8(nu)<=B8(nu).

The total coefficient is80. Each selected factor is owned once. All pairs with a label outside D remain in the original envelope. As in Report695, after remaining-original deletion eta<=nu the true unit contribution stays eta(1); nonunit factors are dominated using the same nu. No correction computed on sigma is substituted for the correction on f sigma.

Use c=1084133/201247200 and g=1-c. The exact changes to the current512 screen coefficients are:

| Screen | Numerical label | Query coefficient removed, divided by c | Remaining coefficient |
|---:|---:|---:|---:|
|32|5|3|0|
|64|25|5|0|
|128|3|3|0|
|160|15|9|0|
|192|75|15|g|
|256|9|5|0|
|288|45|15|g|
|320|225|25|g|

Thus only cW is removed. In particular the original-loss charges at75,45,225 remain. Write the resulting coefficients as C'_j. The new gate is

    G8(nu)=g nu(1)-sum_j C'_j S_j(nu)-c K8(nu).       (CB1)

There are506 positive old budgets, the zero unit budget and five exhausted budgets. The new block is one further budget. This is the existing shared-label mechanism of Reports27/28 and problem-details66 applied to the current source and its complete shallow central block, not a new general clustering theorem.

## Rational dual certificate

The witness contains216,507 legal old-screen rows. Their nonnegative integer numerators sum to10^12 separately in each of the506 remaining positive groups; all other group loads are zero. Unlike696, these old fractions are not held equal to the692 witness. Their coefficients, source, selector menus and legal row domains are unchanged except for the displayed subtraction of query charges.

For the new block, the witness gives225 positive numerators, also summing to10^12. Row r sets b_d=r mod d for every d in D. Such centered layouts are a lawful subset of the full independent-layout menu. They are used only to produce a lower bound on the charged maximum K8, never to identify or restrict that maximum.

Let d_old(x) be the debit from the remaining old budgets and let Hbar(x) be the supplied mixture of n_b(x)^2+2n_b(x). Every charged maximum dominates its feasible mixture. Consequently, for0<=f<=1,

    G8(f sigma)
      <=integral [g-d_old-c Hbar] f d sigma
      <=integral [g-d_old-c Hbar]_+ d sigma
      =U8.                                             (CB2)

The exact margin193/100000-U8 is

    442350474107704309902981337601823784297351
    /13481659352694140862533959680000000000000000000.

Only feasibility and the rational residual integral are used. No optimizer convergence, exact optimum or positive primal field is asserted.

Reports689/690 average and pool the retained measure relative to the fixed comparison reference, preserving its central mod225 marginal and mass and decreasing every remaining nonnegative charged screen. Every complete K8 row depends only on this central residue. Its integral, and hence the full maximum K8, is preserved. Thus the finite category representation still covers arbitrary joint measurable retention; the proof does not restrict f to centered or product fields. The unchanged infinite-height sums remain in all other fees.

## Source extensions and their limits

For the central extension, keep the fixed outside reference and allow a joint central source nu0 on the same actual occupied pure-survivor support S with nu0<=(8/3) Haar|S. Report682 gives domination by R rho0, where R=153832/151875. The same actual deletion map preserves domination. Every retained source in this class is R times a submeasure of sigma, so positive homogeneity of(CB1) and(CB2) give

    R U8=25577252076591987554787560844798176215702649
         /13310150126049343722355200000000000000000000000
        =0.001921635130661273... <193/100000.            (CB3)

This uses a joint density cap; separate central marginal caps are not enough.

The actual cell ratio improves(CB3). In root-major central indices(l,m), multiply each positive residual by

    R_(l,m)=(82/81 if l=4 else1)(1876/1875 if m=10 else1).

Keeping the outside reference fixed gives the sharper upper

    U8_cell=5011656271852541981772045165936683418799413863
            /2639846441666453171600448000000000000000000000000
           =0.0018984650746157942... <193/100000.        (CB4)

The two broader outside-reference envelopes do not fall below target for this witness. Use Report693's arbitrary Borel product references on7,11,13,17,19, each supported off root0 with all other root masses1/(q-1). A single product reference is shared by every cell and query; retention may introduce arbitrary joint correlations. Redistributing the retained measure relative to its common reference as in693 preserves the central mod225 marginal and K8 and does not increase the unchanged screens. Zero-fee terms are omitted; if a positive-fee screen is infinite, set G8=-infinity and the upper is immediate.

Partition the positive residuals into the same eleven actual branches: no outside root1, and each prime's special1 mod q^2 child or other root1 children. After summing all cells, their residual bound has the form

    C+sum_q [A_q t_q+B_q(q-t_q)/(q-1)],  0<=t_q<=q.

For both the original and cell-weighted coefficients, all five slopes are strictly negative. The maximum over one common outside tuple is therefore at t_q=0 for every q. Exact results are:

| Reference class | This witness's upper | Below193/100000? |
|---|---:|:---:|
|Central fixed, root-balanced outside products|0.0019315498829306184...|No|
|Joint central cap and those outside products, uniform R lift|0.001956439055743097...|No|
|Joint central cap and those outside products, cellwise ratios|0.0019329146215378706...|No|

The first and third exact fractions are respectively

    130072415306727502197207084336682462184329
    /67340955807663041271398400000000000000000000,

    299852957966257673729438337346267739596889
    /155129954849059950144000000000000000000000000.

These remain valid upper bounds. Being above target supplies no paying field and proves no limitation of a better dual. The triangle's separate outside-reference obstruction in696 cannot be transferred to the stronger eight-label gate by reversing the inequality between their objectives. No outside parameter is selected separately per central cell.

## Reproduction and remaining scope

The optimizer-free primary verifier checks the supplied budgets and source pins, reuses692's pinned sparse transport, removes only the selected shallow query contributions and computes the new block from literal mod225 residues. It passes1,539,289 explicit checks. The independent verifier rebuilds the source predicates, all remaining row budgets and dense transport in reverse coordinate order, passing5,876,497 checks. Both evaluate every one of2,125,830 positive source states and the same eleven-branch coefficients and32 outside-reference corners. Their exact outputs agree on(CB2)–(CB4) and both broader envelopes.

The retained artifacts are the rational witness, the two verifiers and their exact outputs. Floating search histories are not needed for verification. The all-height and measurable-source conclusions additionally use the ordinary averaging, domination and factor-accounting arguments above; enumeration alone is not their proof.

From the repository root with NumPy installed:

```sh
python3 -I -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/clustered109-central-block-dual-verify/clustered109_central_block_dual_verify.py --output /tmp/central8_primary_replay.json
python3 -I -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/clustered109-central-block-dual-verify/clustered109_central_block_independent.py --output /tmp/central8_independent_replay.json
```

The remaining directions include shared query factors involving outside primes, coupling with deeper central labels, changing the source or head interface with its original conditions preserved, and the unproved bridge to arbitrary finite distinct odd original families. A below-target upper for the present source and gate is a method obstruction, not a proof or refutation of unrestricted Erdős#7.
