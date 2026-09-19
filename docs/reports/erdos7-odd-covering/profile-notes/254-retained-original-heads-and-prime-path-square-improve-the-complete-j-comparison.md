[Index](../marked_head_profile.md) · [Previous complete comparison](250-joint-quadratic-factorial-and-survival-bounds-improve-the-complete-j-comparison.md) · [Retained original heads](251-two-retained-original-tests-sharpen-the-complete-j-heads.md) · [Complete prime-path square](253-two-complete-prime-path-blocks-sharpen-the-j-square.md)

# Retained original heads and prime-path square improve the complete J comparison

On both entire actual saturated J faces, the complete original52-cost
comparison satisfies

    comparison <=429.671383684989083932151846680... .       (RJ1)

The improvement over250 is8.283783552834183331745394087... . All52
original costs, their positive weights, the signed actual mass, outside
square, four AP11 blocks, AP13 and complete infinite count tail remain.
The new inputs are251's three complete original heads and253's complete
square inequality.

Fresh independent moment witnesses give the outward decimal method bracket

    [429.6713836849827, 429.6713836849891].                  (RJ2)

Its exact width is6.3428029878438695...*10^-12. This brackets the best
comparison of the specified independent scalar-moment method under all24
updated constraints. It remains above403. The witnesses certify this
method boundary and do not assert actual-source attainment or a lower
bound for methods retaining additional joint information.

## Four stronger bounds on the same original functions

Retain250's actual source domain, raw mass1/4, survivor mass S=3/20,
common late parameter theta in[1/135,1/90], and all24 basis functions.
Replace only these four upper bounds:

| Basis function | New complete upper | Source |
| --- | ---: | --- |
| n^2 | 5509/1200 | 253 |
| H4(n)=(n-4)_+ | 225629041830357889/1157625000000000000 | 251 |
| original cost0 | 5.694565687831699609719876961... | 251 |
| original cost16 | 4.550682696982637133600824798... | 251 |

The exact last two bounds are

    1791636462292567187058853909283901779303/314622143374512991758741000000000000000,
    165366610325299466178084118303859134302751/36338857559756250548134585500000000000000.

The mean16/25, complete factorial6313/7200, both247 quadratic-cost
bounds, all four249 AP11 bounds and remaining scalar inequalities retain
their full original meaning. Write the updated constraints as

    <1,mu>=S,   <b_j,mu><=B_j for j!=mass.                  (RJ3)

There are24 basis functions and23 upper inequalities. Each inequality is
uniform over the original admissible test labels. All24 therefore apply
to any one target's load, while different target functions continue to
use independently chosen original tests. No cost optimizer or moment
witness is identified with another as one actual family.

The consumer checks the common geometry and full source closure. Each251
head is reconstructed as its exact constant plus positive hinges on all
positive integers, using values at1,...,8 and its affine continuation.
Its adoption is the minimum of the complete new source bound, preceding
bound and complete mean-only bound. The original135 and125 contributions
and every infinite remainder are included through251. The complete
square5509/1200 retains both prime paths and all remaining cross and tail
blocks from253; no finite square head replaces a complete moment.

## Exact envelopes for all original costs and outside terms

For each of the52 original costs and seven outside targets, retain
rational coefficients y_j with

    f(n)<=sum_j y_j*b_j(n), n>=1 integer,
    y_j>=0 for j!=mass.                                    (RJ4)

The mass coefficient is unrestricted because mass is exact. Integration
gives U_f=sum_j y_j B_j. The verifier checks every envelope at1,...,8 and
its entire affine or quadratic continuation from9. An affine gap must
have nonnegative slope. A quadratic gap must have nonnegative leading
coefficient and is checked at9 and the neighboring integers of its vertex.
These are exact whole-load checks with no exponent cutoff or tolerance.

The59 envelopes have166 nonzero coefficients and pass472 low-load
inequalities and59 complete-tail checks. Every target upper is at most
its250 upper;28 improve strictly. The canonical consumer uses only
Python's standard library and exact rational arithmetic.

## Reassemble the entire comparison

Use the original positive weights w_i, signed mass coefficient cS,
outside-square coefficient cQ and offset C0. The complete numerator is

    Nbar=cS*S+sum_(i=0..51)w_i*U_(cost-i)+cQ*U_square
        =34.560314945285335454309534951... .                 (RJ5)

The largest weighted payments are

| Original index | Weighted upper payment |
| --- | ---: |
|0|5.694565687831699...|
|41|4.236606712826775...|
|16|4.015308262043503...|
|47|2.982356984228751...|
|32|1.925148555705559...|
|7|1.743273347527511...|
|46|1.724638054253438...|
|1|1.531353576911854...|

All52 payments occur in(RJ5). The full count law gives

    Tcount=(U_mean-S)/7986+S/87846=277/4392300,

    Ebar=S-U_H4/6-(sum_(e=0..3)U_(AP11-e)+Tcount)/7
        =1343537487631954048096231/15864065217000000000000000
        =0.084690618025965598127699061... .                 (RJ6)

The scalar envelope for the fourth AP11 block is slightly sharper than
its direct249 bound, as in250. All four blocks and the entire count tail
remain. Both Nbar and Ebar are strictly positive, so C0+Nbar/Ebar gives
(RJ1). The remaining403 deficit in numerator units is

    (403-C0)*Ebar-Nbar=-2.258815967889381271741905808... .    (RJ7)

No cost, signed-mass payment or count outcome is assigned zero by omission.

## New witnesses certify this updated method's boundary

Each target f has its own finitely supported rational measure mu_f
satisfying all24 updated constraints(RJ3). Their253 positive atoms pass
1416 exact moment checks, including exact mass. These are fresh witnesses
under the stronger constraints;250's method lower bracket is not reused.
Put L_f=<f,mu_f>. Any valid independent envelope using only(RJ3) obeys

    U'_f >= sup_(mu satisfying RJ3)<f,mu> >= L_f.                (RJ8)

Substituting the L_f in the full formulas(RJ5)--(RJ6) gives Nlo>0 and
Ehi>0. Every valid tuple of such independent envelopes with a positive
denominator satisfies

    N'>=Nlo,   0<E'<=Ehi,
    C0+N'/E'>=C0+Nlo/Ehi
             =429.671383684982741129164002810... .         (RJ9)

The fixed signed mass, positive cost and square weights, and positive
denominator deductions justify this monotone substitution. Separate
witnesses need not coexist on one actual source and need not be realizable
by original covering families. The lower endpoint only limits the
specified independent scalar-moment method with the updated24 bounds.

## Exact artifact and boundary

The [consumer](../frontier/j_face_retained_pair_complete_moment_cost_comparison.py)
and [certificate](../certificates/source_norms/j_face_retained_pair_complete_moment_cost_comparison.json)
retain86 source pins, all24 updated bounds, every original cost and weight,
all59 exact envelopes and fresh witnesses, full signed numerator and count
law, and the exact method bracket. The canonical verifier recomputes the
complete consumer; its pinned source certificates retain the separate
complete source scans.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j_face_retained_pair_complete_moment_cost_comparison.py --check
```

This improves the full comparison on both saturated actual J faces. The
method bracket remains above403. It supplies no off-face neighborhood,
global join, unrestricted Erdos7 result, actual-family attainment claim
or Lean verification.
