# An actual-phase obstruction and source repair for joint debits

A single explicit family separates two questions. Its exact joint deletion cost under the product source of Reports591–598 exceeds the entire raw budget of Report598, even after all genuine old zero sets are used. Nevertheless, an explicit different common source avoids its complete seven-prime family and has a positive all-height continuation gate.

The obstruction concerns the method that combines a fixed inherited worst-case gate with a product-source deletion bound. It is not a covering example, not a computation of the actual deletion mass under the thinned Report598 law, and not an obstruction to re-estimating the gate and deletion together. The positive repair applies to the fixed phase family below; it does not admit the remaining ninety labels with arbitrary phases. These are ordinary proofs with exact finite arithmetic, not new Lean verification.

## One finite family with every relevant old slot present

Put

    P0={3,5,7,11,13,17,19}, V={7,11,13,17,19}.

Use the actual pure originals

    2 modulo3, 7 modulo9,
    4 modulo5, 2 modulo25,
    q-1 modulo q for every q in V.

There are nine pure originals on P0. No higher pure original is present.

Let B598 contain every mixed max-exponent-two label allowed by [Report598](598-high-support-central-squares-preserve-the-common-survivor-law.md). Its exponent vector is in {0,1,2}^7, has support at least two, and satisfies

    both central exponents <=1, or support >=5.

All 1,759 such labels are present. In each original, set every present central coordinate to zero and every present outside coordinate to one, at its full prime-power height. CRT determines one fixed residue per numerical modulus.

Also make all 190 labels of [Report603](603-two-support-four-slices-reduce-the-core-gap-to223.md) present, with exactly the same phase rule. Call their union A190 and put B190=B598 union A190. Including the pure originals in these zero sets does not change any source mass below, because the source already avoids them.

Finally, let R90 contain the complete remaining support-four slice:

    3^a 5^b q^u r^v,
    (a,b) in{(2,1),(1,2),(2,2)}, q<r in V,
    (u,v) in{(1,1),(1,2),(2,1)}.

All 3*10*3=90 originals are present. Their full central residues are one, and their full outside residues are zero. Every phase is fixed globally. The complete seven-prime family has

    1759+190+90+9=2048

pairwise distinct odd numerical moduli. No old slot used for the argument is missing. All original heights are at most two.

## The unchanged actual pure-survivor source

Use precisely the product source rho prescribed by Report591 for these actual pure originals. At3 it is normalized Haar on the five surviving mod9 words

    0,1,3,4,6,

with mass1/5 each. Its root masses are3/5 and2/5. At5 the four retained roots have mass1/4 each. The root2 has four surviving mod25 children, with mass1/16 each; every other retained root has five children, with mass1/20 each. At each q in V, the q-1 retained roots have mass1/(q-1), with uniform deeper digits.

This is one actual product probability on the pure survivor, not a collection of independently selected marginal caps. Its densities obey

    rho_3<=9/5 H_3<2H_3,
    rho_5<=25/16 H_5<5/3 H_5,
    rho_q=q/(q-1) H_q on its support <=q/(q-2) H_q.

Thus the existing uniform bound rho<=3458/405 H_(P0) is retained. The same cylinder inequalities hold at every higher resolving height by uniform lifting.

Let C be the union of the three central predicates occurring in R90. The225 predicate is the intersection of the45 and75 predicates. Therefore

    rho(C)=rho_3([1]_9)rho_5([1]_5)
          +rho_3([1]_3)rho_5([1]_25)
          -rho_3([1]_9)rho_5([1]_25)
          =(1/5)(1/4)+(2/5)(1/20)-(1/5)(1/20)
          =3/50.                                             (JD1)

Every point of C has both central first digits equal to one.

## The exact joint debit is a 243-atom calculation

For an outside tuple write N0 for the number of coordinates with root zero and N1 for the number with root one. At each q the probabilities of the three categories zero, one and other are

    1/(q-1), 1/(q-1), (q-3)/(q-1).

The following equalities use actual literal cylinders.

First, all R90 height-two outside cylinders lie inside the corresponding two-root-zero cylinder with the same central projection. Every such root-pair label is itself present in R90. Hence

    R90=C intersection{N0>=2}.                                (JD2)

Second, any old class with a central component is disjoint from C: its central root is zero where C has root one. Every old class without a central component requires at least two outside roots equal to one. Conversely, all ten uncentred qr originals are present with these phases. Thus on C,

    B598={N1>=2}, and B190={N1>=2}.                            (JD3)

The190 added classes all have a zero central component and therefore do not change JD3.

There is also a global simplification. Call a central root zero bad, and an outside root one bad. Every old or190-added mixed cylinder is contained in a first-level pair cylinder requiring two bad roots. All21 first-level pair cylinders are already actual B598 originals. Hence on the full seven-coordinate space,

    B598=B190={at least two bad roots among the seven coordinates}. (JD3a)

The190 additions are redundant in this particular phase family: their actual additional deletion cost is zero. Their previously proved uniform worst-case fee is not needed to obtain the obstruction JD5.

Independent enumeration of the3^5=243 outside atoms and the bivariate polynomial

    product_(q in V)[(q-3)/(q-1)+x/(q-1)+y/(q-1)]

give

    Pr(N0>=2,N1<=1)=7109/103680.

Consequently the exact joint source debit is

    rho(R90 intersection B598^c)
      =rho(R90 intersection B190^c)
      =(3/50)(7109/103680)
      =7109/1728000
      =0.004114004629629629... .                              (JD4)

There is a real saving: rho(R90)=97/23040, and the sum of the uniform individual source caps is18847728967/1616245488000. But the exact saving does not cross the required inherited budget.

Indeed, with the unchanged continuation constant c=1084133/201247200,

    K598/(1-c)
      =26345885990886052732242307711
       /9006401163337598433853440000000
      =0.002925240116788533... <7109/1728000.

Even using the larger Report598 gate, the proposed lower expression is

    K598-(1-c)rho(R90 intersection B598^c)
      =-10706490091386509343142012289
        /9055182074115772514304000000000 <0.                  (JD5)

The smaller K190 budget also fails. Thus no all-phase upper bound for this exact debit can lie below either threshold. Starting again from K598 and jointly paying a larger new class does not cure the example: that union still contains R90 and its exact debit is at least JD4. This statement grants the190 additions for free when testing JD5, so it cannot be explained by charging them twice.

Missing old classes offer no uniform rebate from their nonexistent zero sets. Here the obstruction is stronger: all1,759 old mixed slots and all190 later additions are actual, present and phase-fixed. Auxiliary classes may be added only by constructing and charging their additional restrictions; the comparison polynomial's negative terms cannot be treated as actual zero sets.

JD5 does not evaluate eta598(R90), and it does not bound the actual gate of this particular eta598 from above. The gap may arise from combining the inherited worst-case gate with a debit whose large values occur in a different regime. A phase-dependent gate/debit estimate or an explicitly changed common source is a different method.

## An explicit replacement source succeeds on this same phase family

Define one product probability sigma by conditioning head Haar on

    x_3=0 modulo3,
    x_5=1 modulo5,
    x_q notin{1,q-1} modulo q for every q in V,

and leaving every deeper digit uniform. Its density bound is

    sigma<=D_sigma H_(P0),
    D_sigma=3*5*product_(q in V)q/(q-2)=1729/45.                (JD6)

This deliberately replaces rho; the larger density constant is carried through the whole new calculation.

The measure sigma avoids every one of the2,048 core originals. A listed pure original has a forbidden first root. Every sigma point has exactly one old bad root, namely its3-root, so JD3a excludes the complete old and190-added mixed union. Every R90 original requires the3-root one, which sigma excludes. The producer also checks the exact zero mass of each literal original separately.

At a prime p, let n_p be the number of retained roots: n_3=n_5=1 and n_q=q-2 for q in V. A positive-depth cylinder has sigma-cap

    C_p(e)=1/[n_p p^(e-1)], e>=1, and C_p(0)=1.

For any one globally fixed complete query layout at finite height Q, expand its squared load as a sum over divisor pairs. Two query cylinders have either empty intersection or one cylinder at their least common multiple. The number of exponent pairs whose maximum is e is2e+1. The standard product-cap estimate therefore gives, uniformly over all layouts and finite heights,

    Gamma_Q(sigma)
      <=product_(p in P0)[1+sum_(e>=1)(2e+1)C_p(e)]
      =7*(43/8)*product_(q in V)
           [1+q(3q-1)/((q-2)(q-1)^2)]
      =75428728493069/424019059200
      =177.88994823813098... <1/c.                            (JD7)

This uses the complete lcm-pair counting estimate already used for query moments in Reports591–592. It does not claim that all maximizing query intersections are simultaneously attained. Every query is tested against the same sigma.

No core deletion remains under sigma, so its mass is one. Equations JD6–JD7 yield

    K_sigma=1-c Gamma_upper
      =508267814751123689/12190378344376320000 >0.             (JD8)

The existing capped continuation at23,29,31 consumes this common law, its complete query bound and its density. It does not require the special pure-balanced construction of rho. Reconstruct those kernels on sigma, using the usual controls and multiplier200/33. All originals touching those three primes may have arbitrary globally fixed residues and arbitrary finite heights. The resulting ten-prime survivor has

    H(U)>=33K_sigma/(200D_sigma)
      =508267814751123689/2838675307397529600000
      >1/5600.                                              (JD9)

Only the core phase family stated above is covered by this repair. No all-phase conclusion for R90 is inferred.

## A literal survivor and exact verification

For a concrete ten-prime instance, add the three pure originals q-1 modulo q at q=23,29,31. The full2,051-label family has the avoiding integer

    341883538591393801 modulo486343645127264925.

Its complete coordinate words are1 modulo9,1 modulo25,2 modulo q^2 for every q in V, and0 modulo each of23,29,31. Direct reduction checks that it misses every listed class. This witness is separate from the source sigma; it confirms that the method obstruction is not a covering example.

The [producer](../../frontier/cover-geometry/joint_source_debit_obstruction.py) and [data](../../frontier/cover-geometry/joint_source_debit_obstruction.json) retain all literal CRT residues, the complete inventory, actual pure-source masses, central and outside atoms, the exact negative comparisons, the replacement-source query factors and positive gate, and the explicit survivor. Their49 named predicates pass8,561 evaluations with optimization enabled. Every old and190-added cylinder is checked against an actual containing first-level pair. Query-tail checks use exact finite-prefix remainders; no original or query truncation replaces an all-height bound. No inherited head scan is rerun.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/joint_source_debit_obstruction.py
