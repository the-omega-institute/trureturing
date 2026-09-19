[Index](../marked_head_profile.md) · [Complete factorial head](241-one-original-j-head-controls-complete-square-and-factorial-moments.md) · [Joint actual survivor](244-three-complete-j-heads-share-raw-survivor-and-marked-deletion.md) · [Previous complete comparison](246-the-joint-j-heads-and-square-improve-the-complete-cost-comparison.md)

# Two original J quadratic costs share hinges and factorial head

On both entire actual saturated J faces, the two original independent
quadratic costs satisfy

| Original cost | Complete upper | Improvement over246 |
| --- | ---: | ---: |
|47, integral of(A^2-81/4)_+|3.345568999029196005291005291...|0.054343362421605463509441097...|
|48, integral of(A^2-9)_+|3.932749181154125877335061008...|0.034867372134814694093510420...|

Their exact upper bounds are respectively

    U47=126462508163303609/37800000000000000,
    U48=145684760666673439/37044000000000000.             (QJ1)

Each row uses its own original positive integer load A and the same
unnormalized actual survivor measure of mass3/20. Uniform source bounds
apply separately to these two tests; their independently chosen labels
are not identified. Each bound covers all6,250,000 containing choices,
the entire common late interval and every omitted exponent and pair.

The improvement comes from retaining the hinge terms and the actual
factorial head in one876-variable source/survivor/deletion LP. It does
not replace the complete factorial moment by a bound for a selected
finite head. The entire distinct omitted-pair payment remains5089/7200.

## Exact all-integer identities for the original costs

Put H_t(n)=(n-t)_+ and Phi5(n)=(n-5)_+*(n-4)/2. For every integer n>=1,

    (n^2-81/4)_+=(19/4)*H4(n)+(17/4)*H5(n)+2*Phi5(n),
    (n^2-9)_+=7*H3(n)+2*H4(n)+2*Phi5(n).                (QJ2)

These are the unchanged original cost47 and cost48 functions. Their
values at1 vanish. The checker verifies the finite transitions and the
leading, linear and constant coefficients of the entire polynomial
continuation, using the original source cost inventory. All hinge
coefficients are nonnegative.

Within either row of(QJ2), write the same original test as

    A=B+O+Z,  B=1+I3+I9+I5+I15+I45.                    (QJ3)

Here O contains all old labels outside the six-label head and Z contains
all positive-seven labels. The original shallow layout fixes B throughout
that row. The factorial inequality from241 is

    Phi5(A)<=Phi5(B)+(B-4)_+*(O+Z)
               +(O+Z)*(O+Z-1)/2.                    (QJ4)

The complete cross bounds use h=(B-4)_+ and
G=I3*I9*I5*I15. With241's complete old-tail operator T and raw old-label
operator R_theta, they are

    C(theta)=T(w*h)+[R_theta(I45)+R_theta(G)]/5.         (QJ5)

The indicator inequality h<=I45+G retains both original rectangles even
when they coincide. The unordered distinct-pair term in(QJ4) is bounded
by the complete241 partition

    Ptail=POO+POZ+PZZ=5089/7200.                        (QJ6)

Its old-old, old-positive-seven and positive-seven-positive-seven series
include all exponent heights. Both costs multiply(QJ6) by2 exactly once.

## One actual source, survivor and late coordinate

Use precisely244's necessary LP: raw mass X of total1/4, actual survivor
Y of total3/20, four independent selected-event projection simplexes,
complete deep-three and deep-five deletion marginals, and the ten marked
residual inequalities. Its876 variables,587 inequalities and16 equalities
are unchanged. The selected events25,27,75,81 retain their original
independent projections and the audited null-event conventions.

The one normalized late coordinate satisfies

    theta=1/135+(1/270)*x,  0<=x<=1.                    (QJ7)

Both opposing raw-cap movements use this same x. No K-domain numerical
bound or forced27 location is assumed.

For a fixed shallow layout and the original21/35/63/105 projections,
let J_a(X,Y) denote244's raw seven-increment and retained-survivor hinge
objective with coefficients a_t from(QJ2), and let K_a be its complete
omitted-label constant. The complete target upper is obtained from

    J_a(X,Y)+2*sum_(c,s,m)Y_(c,s,m)*Phi5(B_(c,s))
      +2*[C0+(C1-C0)*x]+K_a+2*Ptail,                 (QJ8)

where C0=C(LO), C1=C(HI). The factorial head is charged to the same actual
Y columns as the hinges. Neither deletion correction is subtracted again
outside the LP: its constraints already control the residual w*X-Y.

The cross function C is convex in x. Its old-tail term is constant, and
each remaining term is a maximum of finitely many affine raw-source LP
values. Therefore

    C(theta)<=C0+(C1-C0)*x                             (QJ9)

throughout(QJ7). The secant slope in(QJ8) is attached to the same LP x
column; it may be negative. Feasible rational duals are checked against
that signed objective coefficient as well as every other column. No
independent endpoint maximization replaces this common-parameter bound.

The canonical checker reconstructs241's components for all12,500 shallow
layouts at both endpoints, including its original component digest and
factorial-head maximum79/450. It separates the actual Phi5(B) head from
the two cross terms before constructing(QJ8).

## Complete enumeration and exact rational certificates

For pruning, add the same endpoint secant of241's complete factorial head
to each of219's two complete affine hinge bounds. At a two-projection
branch their maximum endpoint value is a valid bound. At a remaining
four-projection branch, maximize the minimum of the two affine functions
over x in[0,1], checking both endpoints and every strict interior crossing.
An unpruned branch takes the minimum of this old whole-interval bound
and a new exact dual upper for(QJ8).

| Target | Two-projection branches | Pruned there | Expanded four-projection branches | Pruned there | New LP branches |
| --- | ---: | ---: | ---: | ---: | ---: |
|47|125000|124997|150|149|1|
|48|125000|124995|250|237|13|

For each target,50 times the pruned-two count plus the expanded-four count
is6,250,000. All branches are covered, including choices that do not require
a new LP. The stored certificate retains the decision digest and an exact
maximizing certificate branch, without claiming that an actual source
attains that branch's upper.

The two targets together retain14 distinct rational duals. For each LP
A z<=b,E z=e,z>=0, every inequality multiplier is nonnegative and the free
equality multipliers satisfy

    A^T*y+E^T*h>=objective                             (QJ10)

in all876 columns. This gives12,264 exact column checks. The objective
key includes the regenerated model and objective. An additional28
unscaled affine evaluations verify the complete original hinge compiler
and its common factorial secant.

The [canonical helper](../frontier/j_face_joint_quadratic_heads.py) and
[certificate](../certificates/source_norms/j_face_joint_quadratic_heads.json)
retain the exact identities, all source pins, complete pair payment, full
model, duals, pruning counts and strict improvements over246. The checker
uses only standard-library rational arithmetic and redoes the complete
component and containing-choice scans. Numerical optimization is confined
to the separate optional proposer; its output is accepted only after(QJ10).

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j_face_joint_quadratic_heads.py --check
```

These are two complete uniform cost bounds on the saturated actual J
faces. They do not themselves provide an updated full52-cost comparison,
an off-face extension, actual-family attainment, Lean verification or an
unrestricted Erdos7 result.
