[Index](../../marked_head_profile.md) · [Original AP11 blocks](242-the-complete-j-survival-and-linear-heads-retain-one-late-split.md) · [Joint actual source](244-three-complete-j-heads-share-raw-survivor-and-marked-deletion.md) · [Complete comparison](246-the-joint-j-heads-and-square-improve-the-complete-cost-comparison.md)

# All four complete J AP11 blocks retain the same marked source

On both entire actual saturated J faces, the four original AP11 block
functions have the following stronger complete bounds:

| Original block | Previous complete upper | New complete upper |
| --- | ---: | ---: |
| AP11-0 | 0.177441526201051799... | 0.175332683230987254... |
| AP11-1 | 0.048934306917473888... | 0.048181657008466204... |
| AP11-2 | 0.005682577085657476... | 0.005620581201878739... |
| AP11-3 | 0.000578406692230884... | 0.000576362872511521... |

Each block retains all6,250,000 original containing choices, the whole
late-split interval and the complete exponent tails. All four use244's
unchanged876-variable joint raw/source/survivor/deletion model. No new
source condition or assertion of LP attainment is introduced.

With244's existing AP13 bound and the same exact mass and complete count
tail, the complete survival denominator satisfies

    E >=41223974541103988888519/488125083600000000000000
       =0.084453710588012873199780385... .             (JA1)

The previous denominator with that same AP13 input was
0.084035777361931397769313488... . The increase is exactly

    51000922730059473727/122031270900000000000000
      =0.000417933226081475430466896... .              (JA2)

These are complete block and denominator improvements. A new full52-cost
numerator and ratio require a separate consumer.

## The original four block functions are unchanged

Write H_t(n)=(n-t)_+ for positive integer loads. The original242 block
functions are F_e(n)=sum_t a_(e,t)*H_t(n), with coefficients

| Block | a1 | a2 | a3 | a5 |
| --- | ---: | ---: | ---: | ---: |
| AP11-0 | 1355/263538 | 20425/263538 | 25/363 | 28/33 |
| AP11-1 | 1355/263538 | 20425/263538 | 25/363 | 0 |
| AP11-2 | 1355/263538 | 2275/263538 | 0 | 0 |
| AP11-3 | 85/87846 | 25/87846 | 0 | 0 |

Every block has F_e(1)=0. The helper consumes242's existing exact count-law
and all-load identity constructor, and checks these coefficients against
the original certified functions before running the new scans. The eleven
other linear functions from242 are not changed by this result.

The count law, including all counts beyond four, remains the same. In
particular its complete remaining contribution is

    Tcount=(16/25-3/20)/7986+(3/20)/87846
          =277/4392300.                              (JA3)

Thus the displayed finite coefficient table does not remove the infinite
count tail from the survival denominator.

## The same actual source retains all marked information

The domain and finite model are exactly244's: actual raw mass1/4,
survivor mass3/20, mean bound16/25 and a common late parameter

    theta=1/135+(1/270)*x, 0<=x<=1.

The876 nonnegative variables consist of400 raw masses X,400 actual
survivor masses Y,25 independent projection weights,50 coarse deletion
masses and the single late coordinate. The587 inequalities and16 equalities
retain all four original selected labels25,27,75,81, their normalized and
absolute source profiles, four mixed intersection caps, both complete
deletion marginals and the ten marked residual inequalities.

The helper checks that the entire regenerated model specification equals
244's certified model. In particular, this does not import the K-specific
forced27 condition, assume a product law for the survivor, identify
independent test residues or exclude source-null events. The original
null-event conventions and actual-source embedding remain244's.

For an original six-label shallow head B and the four independent retained
seven projections21,35,63,105, the complete objective is244's

    sum_(c,s,m,t) a_t *[
      Y_(c,s,m)*(v_t-t)_+ + X_(c,s,m)*g_t(v_t,ell_(c,s))],

    v_1=B, v_t=B+popcount(m) for t>=2.                (JA4)

The actual survivor carries the old hinge and the same actual raw source
carries its positive-seven increment. The complete omitted-label payment
is

    a1*(53/600+1/28)
      +sum_(t>=2)a_t*(2471/81000+1/28).              (JA5)

Every selected label is retained or paid once, and every infinite exponent
tail remains in its original cap series. Deletion information is already
inside the model; no separate deletion saving is subtracted from(JA4).

## Four complete scans and fifteen exact duals

For each original block, there are12,500 shallow layouts, ten independent
21/35 choices and50 independent63/105 choices. The unchanged244 scanner
uses complete219 affine bounds for pruning and the common876-column
source LP for each remaining branch. Both endpoints and any strict interior
crossing of the two old affine bounds are included. A new dual directly
covers the whole late interval; it is not obtained by checking only the
endpoints of a retained LP optimum.

| Block | Two-projection branches | Pruned there | Four-projection branches | Pruned there | Joint LP branches |
| --- | ---: | ---: | ---: | ---: | ---: |
| AP11-0 | 125000 | 124990 | 500 | 498 | 2 |
| AP11-1 | 125000 | 124996 | 200 | 195 | 5 |
| AP11-2 | 125000 | 124996 | 200 | 196 | 4 |
| AP11-3 | 125000 | 124996 | 200 | 196 | 4 |

In each row,50 times the pruned-two count plus the four-projection count
is6,250,000. All reported pruned values are at most the final corresponding
complete block bound. Seed duals are reused when their branch is reached;
the final bank contains exactly15 distinct duals, all consumed.

For each dual, every one of876 rational column inequalities is checked,
with nonnegative inequality prices and unrestricted equality prices.
There are13,140 such exact checks. The reused affine compiler additionally
checks56 unscaled endpoint and common-crossing evaluations. The canonical
verifier uses only Python's standard library, reconstructs the complete
model and all25,000,000 containing choices, and compares every output field
with the certificate. Numerical optimizer status is not part of this proof.

The exact four complete block bounds, in order, are

    18339488712843851089241/104598232200000000000000,
    16362714764780212519/339604650000000000000,
    83986122521866785419/14942604600000000000000,
    102528125119760399/177888150000000000000.           (JA6)

Each is strictly smaller than its prior complete242 bound and its complete
mean-only alternative.

## The denominator retains every original term

The new sum of the four block bounds is

    U_AP11=4004565709269940526273/17433038700000000000000
           =0.229711284313843720559915925... .         (JA7)

Use the already complete244 AP13 bound

    U_H4=22263628571451221/113400000000000000.

With the same unnormalized survivor mass S=3/20 and(JA3), the full survival
inequality is

    E >= S-U_H4/6-(U_AP11+Tcount)/7.                  (JA8)

This is(JA1). Replacing only U_AP11 by its previous sum
337963886/1452753225 recovers the previous denominator displayed above.
Their difference is exactly the decrease in U_AP11 divided by7, proving
(JA2) without changing AP13, the mean or the count tail.

The four independent block optimizers need not coexist on one covering
family. Their upper bounds are uniform on the same actual domain, which
is sufficient for the sum in(JA8); no simultaneous attainment is asserted.

## Exact artifacts and scope

The [helper](../../frontier/j-geometry/j_face_joint_survival_heads.py) and
[certificate](../../certificates/source_norms/j-geometry/j_face_joint_survival_heads.json)
retain all four unchanged coefficient vectors, full source pins, the shared
model, fifteen rational duals, complete scan partitions and every term of
the positive survival denominator.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j-geometry/j_face_joint_survival_heads.py --check
```

This is an ordinary source inequality with exact rational verification on
both entire saturated actual J faces. It does not extend to an off-face
neighborhood, claim a new complete52-cost/global ratio, establish an
unrestricted Erdos7 result or provide Lean verification.
