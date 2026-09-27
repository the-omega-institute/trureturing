# A common pure-tail budget preserves leaf masses and density references

The central mod9 and mod25 boundary can retain its normalization reference without giving each root a separate deletion budget. For one fixed excluded mod9 leaf, six comparison points suffice. For one fixed excluded mod25 leaf, twenty comparison points suffice. The same convex coefficients recover both the leaf masses and the Haar-density multipliers used by all deeper queries.

This is a finite boundary theorem for the pure-source construction of [Report591](591-two-centre-star-boundary-closes-complete-height-three-tails.md) and [Report596](596-a-six-leaf-boundary-admits-the-central-square-label63.md). It preserves the product density constant3458/405. It does not establish a positive all-phase gate, admit any of the remaining413 central-square labels, or resolve unrestricted Erdős #7. The proof below is ordinary mathematics; no new Lean verification is claimed.

## 1. One normalization identity for several groups

Partition a finite live-leaf set into nonempty groups I_j, with n_j=|I_j|. Fix group masses r_j>0 with sum_j r_j=1. Let p>0 be the reference scale and suppose

    0<Delta<=1,    Delta<min_j n_j,
    delta_m>=0,   sum_m delta_m<=Delta.

Write d_j=sum_(m in I_j)delta_m. In units of one depth-two Haar leaf, the surviving raw mass of leaf m is1-delta_m. Retain the joint vector

    v_m = r_j(1-delta_m)/(n_j-d_j),
    beta_j = r_j p^2/(n_j-d_j),       m in I_j.       (PB1)

Here beta_j is the pointwise density multiplier on the surviving subset of group j. It is not an independent choice of an upper bound.

Let X0 be PB1 at zero deficit. For each live leaf m, let Xm be PB1 when all of Delta is assigned to m. Define

    lambda_m = (delta_m/Delta)(n_j-Delta)/(n_j-d_j),
    lambda_0 = 1-sum_m lambda_m.                    (PB2)

Then

    (v,beta)=lambda_0 X0+sum_m lambda_m Xm.          (PB3)

All coefficients are nonnegative and sum to one. Indeed d_j<=Delta gives

    sum_(m in I_j)lambda_m
      = (d_j/Delta)(n_j-Delta)/(n_j-d_j)
      <=d_j/Delta.

Summing over groups proves lambda_0>=0. The condition Delta<=1 keeps every comparison leaf mass nonnegative.

For the density coordinate in group j, its endpoint increment is beta_j(Delta)-beta_j(0), and PB2 gives

    [sum_(m in I_j)lambda_m]
      [r_j p^2/(n_j-Delta)-r_j p^2/n_j]
      =r_j p^2 d_j/[n_j(n_j-d_j)].

Adding the base density r_j p^2/n_j yields PB1. For a live leaf m, the endpoint increments from its own group give

    r_j d_j/[n_j(n_j-d_j)] - r_j delta_m/(n_j-d_j).

Adding r_j/n_j again yields PB1. Other groups leave these coordinates at their base values. Thus the same coefficients prove both parts of PB3.

This is a convex containment. It does not require each comparison point to be realized by a finite family, or assert that all listed points are extreme in every projection.

## 2. A common budget from the actual pure-power inventory

Fix p=3 or5. Distinct original numerical moduli allow at most one original class at each pure-power modulus p^e.

Remove the actual pure-p root when present; otherwise remove one fixed auxiliary root. If the actual pure-p^2 leaf lies in a retained root, use it as the excluded leaf. If it is absent or already excluded by the chosen root, remove one fixed auxiliary leaf in a retained root.

These auxiliary restrictions only shrink the source support. No live original residue is changed, and an auxiliary restriction is not declared to be another original modulus. An original p^2 cylinder in the already excluded root remains avoided automatically.

For each other leaf m, define delta_m as p^2 times the Haar mass of the union of the original higher pure-power cylinders inside m. Distinct leaves and the union bound give the single shared budget

    sum_m delta_m
      <=p^2 sum_(e>=3)p^(-e)=1/(p-1).             (PB4)

Overlap between higher cylinders, with the excluded root, or with the excluded leaf only reduces this sum. It does not allocate a new copy of PB4 to another retained root.

The root and leaf identities remain part of the boundary. Any later relabeling must transport the actual mixed-rule phases along with them.

## 3. The ternary source: six points for a fixed zero leaf

After removing one mod3 root and one retained mod9 leaf, there are five live leaves. Normalize Haar on their complete actual pure survivor as one group. Thus

    n=5, r=1, Delta=1/2.

The six PB3 comparison points are the base and five full-deficit endpoints:

| Point | Live mod9 masses | Haar-density reference |
| --- | --- | --- |
| Base | five entries1/5 |9/5|
| Deficit at one live leaf | one entry1/9, four entries2/9 |2|

The excluded leaf has mass zero throughout. All actual ternary densities are at most2. The two retained mod3 roots consequently have masses at most2/3 each.

Keeping the density reference matters even when the leaf vector is unchanged. The average of the five endpoint leaf vectors equals the base leaf vector, but the average endpoint density is2, whereas the base density is9/5. Leaf masses alone do not recover this normalization reference.

## 4. The quinary source: twenty points for a fixed zero leaf

Balance each of the four retained mod5 roots to mass1/4. The root containing the excluded mod25 leaf has four live leaves; each other root has five. Use

    r_j=1/4,   (n_j)=(4,5,5,5) up to root labels,
    Delta=1/4.

There are twenty PB3 points: the base and nineteen single-leaf endpoints.

At the base, the four live leaves of the affected root have mass1/16 and density25/16. Each other root has five masses1/20 and density5/4.

If the full deficit lies in the affected root, that leaf has mass1/20, its other three live leaves have mass1/15, and the root density is5/3. Other roots stay at their base values.

If the deficit lies in another root, that leaf has mass3/76, its other four leaves have mass1/19, and the root density is25/19. The affected four-leaf root stays at its base values.

In particular every actual quinary density is at most5/3. Giving all four roots an independent excluded leaf and full higher-pure budget is not the actual shared inventory.

The other product-source coordinates retain their existing bounds. Hence the complete seven-prime source still satisfies

    rho<=D H_P,
    D=2*(5/3)*product_(q=7,11,13,17,19)q/(q-2)
      =3458/405.                                   (PB5)

## 5. The same density references control all deeper queries

For any depth-e cylinder inside group j, the actual source mass is at most beta_j p^(-e). Every cylinder of depth at least three lies in one retained first-root group, so no query selects a new normalizer.

The exact raw Haar sums are

| Prime | Original tail, e>=3 | Weighted complete-query tail, e>=3 |
| --- | --- | --- |
|3|1/18|4/9|
|5|1/100|3/40|

The weighted tail uses2e+1: among two divisor exponents, exactly(e+1)^2-e^2 ordered pairs have maximum e. For x=1/p,

    sum_(e>=3)x^e=x^3/(1-x),
    sum_(e>=3)(2e+1)x^e=x^3(7-5x)/(1-x)^2.          (PB6)

Multiply these raw sums by the appropriate density reference before taking the corresponding query maximum. In particular, different quinary root densities cannot be replaced by separately chosen source laws. PB3 transports the leaf masses and these complete-height bounds simultaneously.

The boundary preserves deep-cylinder upper bounds, not the exact microscopic mass of every deeper cylinder.

## 6. What finite gate reduction follows

Fix the phase identities, q factors, retained central-cell mask, coefficient arrays, and one common thinning theta. Each central screen branch uses either the leaf masses or the density references of a given prime. Its products occur across the ternary and quinary vectors. It is therefore separately affine in the two joint source vectors.

Each screen maximum is separately convex. The positive raw-mass and matching-cross terms are separately affine, while subtracted screen coefficients are nonnegative, as in the gate structure of [Report597](597-a-common-pair-survivor-law-closes-the-outside-square-slice.md). The fixed-theta gate is consequently separately concave. PB3 gives

    K(sum_i lambda_i X_i,sum_j mu_j Y_j;theta)
      >=sum_(i,j)lambda_i mu_j K(X_i,Y_j;theta).     (PB7)

For a fixed pair of zero-leaf identities, six times twenty comparison pairs therefore suffice for this fixed-theta check. Retaining all six ternary and twenty quinary zero identities gives36 ternary points,400 quinary points, and14,400 comparison pairs. Symmetry reduction must preserve every declared phase and zero identity.

PB7 uses the same theta at every comparison point. Independent positive choices at different points do not imply an interior positive choice. For example, K(x,theta)=(2x-1)(theta_1-theta_2), theta in[0,1]^2, is affine in x for fixed theta. Its optimized value is1 at both endpoints of[0,1] and0 at the midpoint.

A source-dependent normalized optimization problem is also outside PB7. The old64-template q-factor reduction is not transferred across a changing retained-cell mask. A positive all-phase continuation gate remains unproved.

## 7. Reproducible exact comparison data

The standard-library producer [pure_tail_joint_reference_hull.py](../../frontier/cover-geometry/pure_tail_joint_reference_hull.py) writes [its exact JSON data](../../frontier/cover-geometry/pure_tail_joint_reference_hull.json). It uses explicit checks, including when Python optimization is enabled:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/pure_tail_joint_reference_hull.py

The producer verifies all436 indexed comparison points; twelve allocations for three groups with unequal prescribed masses; eighteen actual finite pure families covering missing, live, root-null and overlapping restrictions; the actual normalization and deeper cylinder bounds of those finite sources; PB6 with exact finite-prefix/infinite-remainder identities; and PB5.

There are19 distinct check predicates and2,911 predicate evaluations. These finite checks verify the implementation and retained data. The general convex identity and arbitrary-height claims are carried by PB1--PB6, not by extrapolating a finite enumeration. No LP positive example, LP zero output or negative dual is used to establish this report.
