# Eight higher pure originals defeat the inherited continuation threshold

Keep [Report680](680-actual-leaf-capacities-separate-generic-and-common-source-gates.md)'s actual 101-original clustered fixture, its weak corner `(4,10)`, its exact outside source and its complete coefficient comparison. Add the following eight globally fixed original classes:

| Original modulus | Residue |
| ---: | ---: |
| 27 | 4 |
| 81 | 13 |
| 243 | 40 |
| 729 | 121 |
| 125 | 2 |
| 625 | 27 |
| 3125 | 152 |
| 15625 | 777 |

All 109 numerical moduli are distinct and odd. Assign the same coarse leaf weights as680 and make each weak leaf uniform on its actual remaining set. For this actual law, every coarse cell field has complete comparison gate at most

    U4 = 970010484735106794674517936604944094739
           /1220679392690694067983395343197798400000000
       = 0.0007946480382510202... < 193/100000.

The same obstruction holds for every finite-cylinder retention field depending only on the two central coordinates, when its queries are charged through the same aggregated all-height deep-sup interface. The proof below uses finite partitions, not differentiation or an optimizer.

This is an obstruction to reaching the stated threshold with the specified conditional source and response interface. The upper bound is positive: it neither proves every field has nonpositive gate nor rules out a positive certificate for a weaker continuation task. It is not a covering: the integer `432297622003171927` avoids every one of the 109 explicit classes. Nor does it rule out a changed conditional source, an outside-dependent field, different coarse weights, or a more precise height-dependent charging interface.

## 1. One nested family of actual pure deletions

At the ternary weak leaf take literal residue `b3 = 4 mod 9`, weight `w3 = 1/9` and reference density `D3 = 2`. At the quinary weak leaf take `b5 = 2 mod 25`, weight `w5 = 1/25` and reference density `D5 = 4/3`. These are exactly680's weak leaves; they avoid the existing pure classes and the central15 mask on their joint cell.

For p equal to 3 or 5, add, for each `1 <= j <= n`, the one actual original

    b_p + p^2 sum_(k=0)^(j-2) p^k modulo p^(j+2).

The empty sum is zero. Reading higher p-adic digits from low to high, the deleted word is `1^(j-1)0`. The words `0,10,110,...` are pairwise prefix-incompatible: at the terminating digit of the shorter word, the longer word has 1 instead of 0. Thus these are disjoint cylinders within the chosen leaf, and the new original moduli are `p^3,...,p^(n+2)`, each used once. Passing from n to n+1 leaves every previously assigned original phase unchanged.

All base101 central predicates resolve modulo225. Consequently these deeper pure deletions do not change which mixed event is active on a coarse cell. Both prime-coordinate constructions coexist on one actual product central law; finite CRT supplies their joint realizations. The outside law and all mixed phases remain exactly those of680. This is not a combination of separately optimized incompatible phases.

The remaining Haar capacity in the weak p-squared leaf is

    t_(p,n) = 1/p^2 - sum_(j=1)^n 1/p^(j+2)
            = (p-2+p^(-n))/[p^2(p-1)].

Making the assigned weight `1/p^2` uniform on that actual surviving set gives normalized density

    gamma_(p,n) = (1/p^2) / [((p-1)/(p-2)) t_(p,n)]
                = (p-2)/(p-2+p^(-n)).

Hence

    gamma3_n = 1/(1+3^(-n)),
    gamma5_n = 3/(3+5^(-n)).

These are at most one, so the original reference density bounds remain valid. The strong leaves retain their original uniform laws and capacities. All coarse weights and the exact coarse outside-source mass `305684996597/646498195200` are unchanged.

At n=4 the capacities and normalized factors are

    t3 = 41/729,       gamma3 = 81/82,
    t5 = 469/15625,    gamma5 = 1875/1876.

There are only eight additional originals, listed above.

## 2. One intact nested query path realizes every deep capacity

The whole next-digit-2 child survives all the deleted words: a deleted word starts in higher digit 0 or 1, whereas this child starts in 2. For every depth `e >= 3`, the cylinder

    b_p + 2p^2 modulo p^e

is therefore entirely contained in the weak leaf's surviving set. These cylinders form one nested path; their higher words are `2`, `20`, `200`, and so on. For p=3 the residues are always22, and for p=5 they are always52.

The actual mass of this depth-e cylinder is

    (1/p^2) p^(-e) / t_(p,n).

Dividing by the reference prefix bound `((p-1)/(p-2)) p^(-e)` gives exactly `gamma_(p,n)`. Thus the same source realizes the sharp normalized central factor at every deep height along a fixed nested path. This does not assert that all charged originals, all outside-root maxima or all different selector maxima are attained simultaneously.

Each finite collection of these nested queries is jointly compatible with the original family. For example, at n=4 choose central residues22 modulo729 and52 modulo15625, and outside residues2 modulo each `q^2`, `q in {7,11,13,17,19}`. CRT gives

    x = 432297622003171927
        modulo 1190750449028765625,

and direct substitution verifies that x avoids all109 explicit originals. The all-height statement is a compatible family of finite prefix queries; it does not claim that one ordinary integer has both distinct prescribed p-adic limits at every infinite depth.

## 3. The unchanged dual certifies a finite obstruction

Reuse680's already supplied nonnegative selector mixtures, with integer denominator `2^32`. All original selector identities, globally fixed outside roots, coefficients and group budgets remain unchanged. Only the weak deep central capacities vary: multiply a weak ternary deep selector by `gamma3_n`, and a weak quinary deep selector by `gamma5_n`. Strong deep entries and all shallow/root/leaf entries stay fixed.

For each cell c, the dual debit has the form

    A00(c) + gamma3_n A10(c) + gamma5_n A01(c)
             + gamma3_n gamma5_n A11(c),

with all four A-values nonnegative and fixed by the inherited literal mixtures. Therefore the all-field upper certificate is

    U_n = sum_c max(0,
              g w_l v_m H_empty(c)
              - A00(c) - gamma3_n A10(c) - gamma5_n A01(c)
              - gamma3_n gamma5_n A11(c)).

This is the same maximum-versus-convex-combination inequality as680. The original fee budgets still hold; no LP optimality or new optimizing field is invoked. The sequence is nonincreasing, and its limit is the old generic upper bound.

Exact evaluation gives:

| n | Dual upper U_n |
| ---: | ---: |
| 0 | 0.0398175376827464... |
| 1 | 0.019212377191181657... |
| 2 | 0.007252343528091848... |
| 3 | 0.002468523328479762... |
| 4 | 0.0007946480382510202... |

The n=4 value is the exact fraction in the opening statement. It is the first value below the target among these five evaluations; the n=3 upper does not show that n=3 can pay the target, or that four is an optimal obstruction depth.

The same upper also applies to680's corrected full-inventory case: replacing each of the four extra guarded mode9 screens by its full mode8 screen increases the fee for every nonnegative field. This is a functional screen domination, not an entrywise comparison of the fee arrays. Subsequent uniform factor thinning multiplies the whole gate and cannot repair the deficit.

## 4. Deeper central retention fields do not repair this interface

Let `theta(x3,x5)` be any `[0,1]`-valued finite-cylinder function of the central coordinates only. Keep exactly the uniform-on-survivor leaf laws above, the outside source depending only on the coarse leaf pair, and the same aggregated all-height normalized deep-sup query interface. Define

    theta_bar(l,m)
      = average of theta on S3_l times S5_m

under the normalized conditional survivor laws. Each `theta_bar` lies in `[0,1]`.

Choose finite depths resolving theta and every deleted pure cylinder. At those depths every surviving prefix atom in a fixed leaf is a complete cylinder, and the base law has the same density on all such atoms in that leaf. Refinement remains possible to any greater depth.

Source mass and every screen without a deep central axis are unchanged by replacing theta with its coarse conditional average: their other factors are constant on the relevant coarse cell.

For a screen with only the ternary axis deep, fix its coarse ternary leaf, its entire quinary selector and its one global outside query root. Normalize the score on each surviving ternary prefix atom by the inherited prefix bound. Averaging these scores over the normalized ternary survivor law gives exactly the corresponding coarse score with `theta_bar`: the common density factor is `gamma3_l`, and the quinary sum and outside response stay inside this fixed average. At least one atom scores at least its average. That atom is an allowed deep query, so the fine deep-sup screen is at least the coarse screen. The same proof applies when only the quinary axis is deep.

When both axes are deep, fix the coarse leaf pair and outside root and average over pairs of surviving prefix atoms. Their normalized score averages to

    gamma3_l * (4/5) gamma5_m * H_T(l,m;root) * theta_bar(l,m),

the coarse two-deep score. Again some actual atom pair attains at least the average. Maximizing over the original coarse selectors and root choices preserves the inequality. The outside root was fixed throughout each average; no pointwise root switching is introduced.

Consequently every deep screen for theta is at least its corresponding screen for `theta_bar`, while all shallow screens and the source mass are equal. All fees are nonnegative, so

    G_deep-sup(theta) <= G_coarse(theta_bar) <= U4.

This direct finite-partition proof handles the mixed deep cases without assuming that two sequential averaging operations commute with a maximum. It also applies to the stronger full mode8 fee case, whose additional screens are shallow in the relevant sense.

The all-height supremum is essential. This argument does not give the same conclusion for a height-specific charging rule capped below the depth needed to resolve theta. In a fixed finite original inventory the aggregated supremum may overcharge the actual queries. Retaining their separate depths or more of their joint geometry is a possible change of interface, not covered by this obstruction.

## Exact evidence and boundary

The standalone standard-library program [clustered_higher_pure_capacity_obstruction.py](../../frontier/cover-geometry/clustered_higher_pure_capacity_obstruction.py) reads only the pinned101 fixture, its exact source table, the fixed680 dual witness and the unchanged640 coefficient input. Its 2,468 explicit checks pass under `python3 -I -S -B -O`; no optimizer or new Lean is used. It checks the disjoint actual higher-pure cylinders, the residual capacities, finite witnesses along the intact query ray, the compatible109-original CRT instance, every inherited dual group and the exact upper fractions. The general nested-ray and finite-partition arguments above supply the unbounded-height and arbitrary finite-cylinder-field conclusions; finite checks do not replace them.

The separately authored [independent verifier](../../frontier/cover-geometry/clustered681_independent_check.py) and its [result](../../frontier/cover-geometry/clustered681_independent_check.json) pass17,389 explicit checks without reading or importing the producer implementation. They reconstruct the literal rational selectors and dual debits, compare all80 residuals and all five depth values exactly, check the109 original classes and avoiding integer, and verify full-mode8 screen domination. These are independent implementations within the same model family. A separate ordinary review checked the finite-partition proof and its global-query quantifier.

Both retained programs were rerun with exit code0 and reproduced their JSON results byte for byte. From the artifact directory:

```sh
python3 -I -S -B -O clustered_higher_pure_capacity_obstruction.py
python3 -I -S -B -O clustered681_independent_check.py --report clustered_higher_pure_capacity_obstruction.json
```

The result shows why weak leaf mass alone cannot sustain680's improvement when actual higher pure deletions are allowed. It locates the failure in the selected conditional source and the aggregated deep-sup interface. It does not eliminate outside-dependent retention, alternate conditional densities, different coarse allocations, sharper height-specific queries, or a different joint boundary construction.
