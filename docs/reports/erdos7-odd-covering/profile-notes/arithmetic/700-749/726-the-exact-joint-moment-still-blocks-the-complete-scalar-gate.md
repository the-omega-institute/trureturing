# The exact joint moment still blocks the complete scalar gate

On the actual 75-row opposite-root head, replacing the separate-cylinder second-moment envelope by the exact shared-layout moment does not repair the scalar criterion of Report 720. For EVERY supported head probability `p`,

    A(p)+Gamma_star(p)/19
      >=14451988566971/14400000000000
       =1+51988566971/14400000000000>1.                (JG1)

Thus that criterion cannot pass at any scalar coefficient `beta>=1/19`, even after optimizing the head source and evaluating the joint moment exactly. The result closes this particular route on one actual head. It does not exclude actual-union replacements of the debit, conditional higher-digit sources, mixed-moment transport, or an uncovered integer.

This is an ordinary dual inequality with an independently reconstructed exact rational certificate, not new Lean verification or a counterexample to Erdős #7.

## 1. The same head source, complete debit, and exact joint moment

The eleven actual originals are

| Numerical modulus | Phase |
|---|---:|
|3|0|
|9|1|
|5|0|
|7|0|
|15|11|
|45|2|
|21|1|
|63|58|
|35|3|
|105|74|
|315|187|

Let `H` be their 75 surviving residues modulo315. A probability `p` on `H` is extended by independent Haar higher 5- and 7-adic digits. Ternary height remains at most two.

For `j=0,1,2` and `E subset {5,7}`, put

    m_(j,E)=3^j product_(q in E)q,
    L_E=product_(q in E)q/(q-1),
    C_(j,E)(p)=max_(a mod m_(j,E))p(x=a mod m_(j,E)),
    A(p)=sum_(j,E)(L_E-1) C_(j,E)(p).                 (JG2)

This is exactly the complete deep-original union debit under this source. It is a sufficient debit, not the actual deleted union in every family.

For finite heights `e,f>=1`, define `Gamma_(e,f)(p)` as the maximum squared complete divisor-query load on `9*5^e*7^f`. Every numerical divisor has its own one globally fixed query phase. Write

    Gamma_star(p)=sup_(e,f>=1) Gamma_(e,f)(p).          (JG3)

[Report 722](722-exact-joint-load-prefix-reduction-and-a-coherent-anchor-counterexample.md) gives the exact first-phase reduction without identifying exponent slots that have the same flattened first-digit modulus. No separate-cylinder upper envelope is substituted in JG1.

## 2. Valid lower witnesses from coherent complete layouts

For an anchor `a mod315`, set

    J_a(x)=1+1_(x=a mod3)+1_(x=a mod9),
    F_a(x)=J_a(x)^2
       * (43/8 if x=a mod5, otherwise1)
       * (44/9 if x=a mod7, otherwise1).              (JG4)

These row vectors are genuine monotone limits of complete shared query layouts. To see this, preserve the anchor's ternary and first nonternary digits, set every later nonternary digit to zero, and use the reductions of that ONE CRT anchor for all numerical divisor slots at each finite height.

Conditional on matching the first `q` root, the finite local squared divisor load has mean

    1+sum_(r=1)^h (2r+1)q^(1-r).

If the first root does not match, only the exponent-zero divisor contributes. The matching expression increases to

    1+q(3q-1)/(q-1)^2,

which is `43/8` at5 and `44/9` at7. Independence of the higher digits multiplies the two factors; the ternary load is the fixed `J_a`. Consequently,

    sum_(x in H)p(x)F_a(x)<=Gamma_star(p)             (JG5)

for every anchor and the SAME `p`. These are valid lower witnesses; no claim that coherent anchors exhaust the joint maximum is needed. Report 722 shows that they do not exhaust it in general.

## 3. One rowwise dual covers all head probabilities

Choose nonnegative rational cylinder weights `lambda_(m,a)` and coherent-layout weights `nu_a`, with

    sum_a lambda_(m,a)<=L_E-1 for m=3^j product E,
    sum_a nu_a<=1/19.                                (JG6)

Define on actual head rows

    g(x)=sum_(m,a)lambda_(m,a)1_(x=a mod m)
            +sum_a nu_a F_a(x).                      (JG7)

By the cylinder maxima in JG2 and each shared-layout inequality JG5,

    A(p)+Gamma_star(p)/19
      >=sum_x p(x)g(x)>=min_(x in H)g(x).            (JG8)

All these inequalities use one probability `p`. Averaging valid query witnesses does not require them to be simultaneously maximizing layouts.

The [rational witness](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_obstruction_witnesses.json) has 15 nonzero cylinder weights and 67 coherent-layout weights. The latter sum to

    52631578913/1000000000000 < 1/19.

Every cylinder budget passes exactly. Reconstructing all 75 rows gives

    min_x g(x)=14451988566971/14400000000000,

proving JG1. No optimizer or floating arithmetic is needed to consume this certificate.

The obstruction is already witnessed at finite height. Keep the same 82 weights and truncate each coherent layout to `e=f=5`, so each has 108 distinct numerical divisor slots in period `472696875`. The exact rowwise minimum becomes

    300936162383991781/300125000000000000>1.           (JG9)

Thus, with the SAME complete debit `A`, even `A(p)+Gamma_(5,5)(p)/19` is uniformly greater than one. The consumer reconstructs a literal common CRT centre for each of the 67 layouts; the independent checker also evaluates the finite conditional digit moments directly. This supplies a finite witness for failure of the complete scalar gate. It does not replace the complete debit by the smaller debit of a truncated actual family.

## 4. What has been excluded

[Report 720](720-weighted-distortion-bridge-and-all-parameter-cylinder-envelope-obstruction.md) proves that all 720 orders and all scalar distortion parameters in its stated six-prime continuation envelope have `beta>1/19`. Since `Gamma_star` is nonnegative, JG1 therefore excludes

    A(p)+beta Gamma_star(p)<1

for all those choices on this actual head. The obstruction now uses a lower bound for the EXACT moment itself. It is stronger than failure caused solely by that report's separate-cylinder upper bound.

The complete debit `A` and the prefix-Haar source are essential scope conditions. Replacing separate pure25/49 charges by their actual joint union changes the functional; choosing higher digits conditionally also changes the source. Neither is excluded. This certificate makes no uniform claim about the other 85-row head, nor does it assert that the actual original family covers.

The [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_obstruction.py) reconstructs the literal head, validates every rational budget, evaluates all actual rows, and checks finite numerical-exponent pair counts against their complete geometric limits. Its result is [retained here](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_obstruction.json). The dual was independently checked from its data. Ordinary proofs supply the limiting-layout and all-probability bridge; these checks are not a Lean endpoint.
