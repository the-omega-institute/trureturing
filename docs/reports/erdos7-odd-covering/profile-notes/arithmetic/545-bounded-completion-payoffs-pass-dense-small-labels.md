# Bounded completion payoffs pass dense small labels

For any finite actual family on Q={5,7,11,13,17,19}, with at most two original classes at each numerical modulus, assume that none of the eight full labels

    11*d,  d in {25,125,49,343,175,875,245,1715}

occurs. Then the unchanged PA law has complete query norm at most

    19147691388545460496117/3800547456524288870400
      =5.03814032256726... <257/51.

All other original phases, multiplicities up to two, and finite heights are arbitrary. In particular two originals at each of 55,77,385 are allowed, as are originals at every higher 11-exponent. The proof supplies a bounded lower witness for the mixed-source debit of [report544](544-missing-original-slots-restore-a-common-law-debit.md). A concrete actual family lies outside every single-pair PD8 test and the PS1 test there, but satisfies this new condition.

This is an ordinary mathematical sufficient condition for the auxiliary two-copy problem. It does not resolve arbitrary two-copy families or unrestricted Erdős #7; no new Lean verification is claimed.

## 1. A bounded lower witness controls the source defect

Retain precisely the actual and completed PA kernels of [report348](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md). Let H be product Haar, U the actual mixed 5/7 forbidden union inside the complete pure survivor, eta=H restricted to U, and delta=1/12-eta(1). The final actual PA subprobability is lambda; it is normalized only once. Report544 PD8a gives, for every actual modulus-35 original C,

    H(C\U)<=delta.                                             (BP1)

Suppose f is a fixed measurable function supported on C, with 0<=f<=M. Choose first-eleven comparison slots of total beta weight beta whose untruncated threshold-two hinges are pointwise at least f. Then

    J11 >= beta integral f d eta
        >= beta[integral f dH-M delta],
    delta+J11/3 >= (beta/3) integral f dH
                       +delta(1-beta M/3).                    (BP2)

The second inequality follows by subtracting the integral on C\U, bounded by M times BP1. It remains valid when the first lower bound is negative. If beta M<=3, the unknown defect has a nonnegative coefficient. All integrals use the same actual eta, and comparison completions change no actual original, kernel or law.

The clipped function f is used only as a pointwise LOWER witness for an untruncated hinge. No convex upper comparison is applied to f; that would require a different argument. The existing convex PA upper comparison and its constants remain unchanged.

## 2. Eight numerical slots give a fixed joint payoff

Fix any actual modulus-35 class C=C5 times C7. Select arbitrary nested cylinder extensions

    A3 subset A2 subset C5, at 5-depths three and two;
    B3 subset B2 subset C7, at 7-depths three and two.

In BOTH exponent-one comparison slots, use the following missing old phases:

| Old numerical cofactor | Fixed phase cylinder |
| --- | --- |
| 25 | A2 |
| 125 | A3 |
| 49 | B2 |
| 343 | B3 |
| 175 | A2 times C7 |
| 875 | A3 times C7 |
| 245 | C5 times B2 |
| 1715 | C5 times B3 |

The absence hypothesis supplies both slots at each of these eight distinct full numerical labels. Thus no original phase is overwritten. Include the unit, retain every other occupied phase, and complete the remaining missing phases arbitrarily once. This is one globally fixed comparison assignment, independent of the realized point and every final query.

On C write S5=1_A2+1_A3 and S7=1_B2+1_B3. Each slot load is at least 1+2S5+2S7, because the mixed companion agrees with its pure cylinder on C. Its threshold-two hinge therefore dominates

    f=1_C min(3,(2S5+2S7-1)_+).                            (BP3)

Under Haar conditioned on C the counts are independent, with

    Pr(S5=0,1,2)=(4/5,4/25,1/25),
    Pr(S7=0,1,2)=(6/7,6/49,1/49).

The payoff is zero at S5+S7=0, one at S5+S7=1, and three otherwise. Thus

    Pr(f=0 | C)=24/35,
    Pr(f=1 | C)=288/1225,
    Pr(f=3 | C)=97/1225,
    integral f dH=579/(35*1225)=579/42875.                (BP4)

Both exponent-one beta weights are 5/11. Applying BP2 with beta=10/11 and M=3 gives

    J11 >= (10/11)[579/42875-3 delta],
    delta+J11/3 >= 386/94325+delta/11 >=386/94325.         (BP5)

All omitted debit terms, including every higher exponent, are nonnegative. No finite truncation of the actual family or the final query carrier has been made.

## 3. Uniform strict bound under the absence condition

Set T=257/51 and retain the report348 NC4 constant

    c0=6168733163201163811/542935350932041267200.

The unchanged same-law PA credit from BP5 alone is at least

    (T-2)*386/94325=11966/962115.

Its excess over c0 is

    Delta=4086970802426556683/3800547456524288870400
         =0.0010753637072497472... >0.                    (BP6)

When delta<1/35, an actual modulus-35 original exists: a missing copy there costs 1/35 of the total raw mixed capacity. Apply the construction to one such C. When delta>=1/35, the direct packing credit already exceeds the same lower bound, since

    (T-2)/35-11966/962115=71579/962115>0.

The pure-deficit credits and all other debits in report544 PD3 are nonnegative. Its PD1-PD2 therefore give, for every finite complete final query under the same lambda,

    E_(lambda/lambda(1))(L-1)<=T-Delta/lambda(1)<=T-Delta.

Here 0<lambda(1)<=1 is the existing PA subprobability guarantee. The comparison assignment was fixed before choosing any final query. Take each numerical label's maximizing phase under that one law, then exhaust the labels to retain all query heights. This proves the stated complete-query bound.

## 4. Strict extension beyond all previous single-pair tests

Take the following fixed old family at N=4. For p=5,7 and 1<=e<=4, use the two pure originals p^(e-1),2p^(e-1) modulo p^e. For every 1<=a,b<=4, use two mixed originals with coordinate phases

    (3*5^(a-1),3*7^(b-1)), (3*5^(a-1),4*7^(b-1))

at modulus 5^a*7^b. Add the following six originals, with no other original involving 11:

| Full numerical label | Old phase | Two 11-digits |
| --- | --- | --- |
| 55 | 4 modulo 5 | 1,2 |
| 77 | 5 modulo 7 | 3,4 |
| 385 | (4 modulo 5,5 modulo 7) | 5,6 |

Finally add one pure original 1 modulo each of 13,17,19. There are 57 originals on 30 numerical labels. The all-zero point survives. Every class has a private point: take 11 and later coordinates zero for the old classes, the respective unique 11-digit and an old surviving point for each new 11-class, and all other coordinates zero for each final pure class. CRT realizes these coordinate witnesses.

For this same actual old source,

    eta(1)=4992/60025, delta=121/720300,
    d5=1/1250, d7=1/7203.

For ANY pair of distinct nonunit old 5/7-smooth cofactors touching {5,7,35}, report544's missing-slot weight is Gamma=1/11: the exponent-one maximum occupancy is two and all higher occupancies are zero. Thus for every common cylinder R,

    Gamma eta(R)<=eta(1)/11<=1/132<1/125.

If neither cofactor is in {5,7,35}, their lcm is at least 125, so Gamma eta(R)<=H(R)<=1/125. Indeed the only remaining old cofactors below 125 are 25 and 49, whose lcm is 1225. Consequently the entire PD8 left side, even after choosing its best pair and cylinder, is bounded above by

    A5*d5+A7*d7+A57*d5*d7+(T-2)delta+(T-2)/(3*125)
      =92153606998216691157721/9145067317261570094400000.

The A constants are precisely those of report544 PD3. This upper bound is below c0 by

    921646448584542100691/717260181746005497600000>0.       (BP7)

The PS1 criterion there also fails: each actual modulus-35 class is (3,3) or (3,4), both copies at all three full labels have old phases missing either C, and all usable counts s_d(C) vanish.

Nevertheless all eight required full labels are absent, so BP6 proves the strict bound under the same PA law. This exhibits a family certified by the new region and by none of the older single-pair PD8 or PS1 tests. It uses the general report544 debit identity itself; it does not claim that identity fails, that the older regions are contained in the new region, or that failure of a sufficient test is a lower bound on an actual law.

## 5. Remaining problem

The argument controls an uncertain removed-source shape by bounding the payoff before subtracting its defect. It still requires the eight specified exponent-one labels to be absent. Dense occupancy of those labels, arbitrary two-copy closure, and the separate joint ternary transport to the unrestricted original problem remain unresolved.

[Report546](546-dense-irredundant-families-separate-stage-debits-from-actual-unions.md) constructs dense irredundant families in which every fixed label is eventually occupied twice and the best credit from all four stage completions tends to zero. The same PA law is nevertheless certified below257/51 by retaining shared current-prime phases in the actual forbidden union. Thus higher missing-slot lists alone cannot force a uniform positive stage credit; the general problem still requires a joint saving beyond those debit terms.

## 6. Independent exact finite checks

The standalone [consumer](../../frontier/cover-geometry/bounded_descendant_debit.py) and [retained result](../../frontier/cover-geometry/bounded_descendant_debit.json) contain explicit rational inputs and import no previous producer. The recorded execution exited0 with47 named checks passing.

It reconstructs all1225 equal-Haar-mass descendants of one actual35 cylinder directly from congruences. The eight numerical phases give the literal load in BP3, with payoff histogram840 zeros,288 ones and97 threes. It checks the most damaging deletions at all1226 whole-cell and1225 half-cell masses, retaining the three breakpoints of the fractional deletion envelope. These are finite controls on the bounded-loss estimate; BP1-BP2 prove its arbitrary-measurable-source statement.

The same consumer constructs all57 originals of section4, checks all57 private points and the all-zero survivor, and reconstructs the old mixed mass and pure deficits. Exact arithmetic verifies BP6, BP7, the universal single-pair upper estimate and both actual35 classes' zero PS1 usable counts. The all-height theorem is the ordinary argument above, not an extrapolation from the finite fixture.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/bounded_descendant_debit.py
```
