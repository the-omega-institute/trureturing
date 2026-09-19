# Exact seven-retained head and slope sharpen the complete J factorial

On both entire actual saturated J faces, the complete pure factorial
function `Phi5(n)=(n-5)_+(n-4)_+/2`, applied to the original load
`A` on the actual survivor measure `mu`, satisfies

\[
 \int \Phi_5(A)\,d\mu\le
 \frac{130204314611580731}{165375000000000000}.
\]

The previous complete six-retained bound in
[284](284-exact-retained-head-and-slope-sharpen-the-complete-j-factorial.md)
was `782845887531143161/992250000000000000`. The exact reduction is
`64799994466351/39690000000000000`.

This combines the exact retained-head treatment of 284 with the existing
seven-label model of
[282](282-seven-retained-old-labels-strengthen-the-complete-j-moments.md).
The retained old labels are `25,27,75,81,135,125,225`; every original
6531-variable constraint, all 11211 inequalities, 19 equalities,
independent residue profiles, and the common late parameter are preserved.

For an original head count `B`, retained count `R`, and
`h(B)=(B-4)_+`, define

\[
 G(B,R)=\Phi_5(B)+h(B)R+\binom R2-\Phi_5(B+R),\qquad
 D(B,R)=h(B)+R-h(B+R).
\]

For all relevant counts,
`D(B,R)=min(R,(4-B)_+)>=0`, `G(B,R)>=0`, and
`G(B,R+1)-G(B,R)=D(B,R)`. The certificate checks the 48 combinations
`1<=B<=6`, `0<=R<=7`. For every nonnegative integer `x,T`, the inherited complete inequality is
`Phi5(x+T)<=Phi5(x)+(x-4)_+*T+binom(T,2)`. It is equality for
`x>=4`; for `x<4`, its left side is
`binom((T-(4-x))_+,2)<=binom(T,2)`. Thus it has no load cutoff.
Starting this inequality at `B+R` gives the exact survivor head `Phi5(B+R)`. Remaining old events and
unselected positive-seven events retain their original, possibly larger,
`h(B)+R` slope payment.

For the selected positive-seven events, apply their raw conditional cap
directly to the new nonnegative integrand `h(B+R)`. At a cell the complete
cap weight is

\[
 W=\frac15+\frac6{35}m_1+\frac6{245}m_2.
\]

The new raw expression is `W*h(B+R)`. The previous cap expression
minus this new expression equals `W*D(B,R)`; this is an identity between two justified
cap expressions, not subtraction of an upper bound on an unknown
actual integral.

For the four-bit base mask with `q` marked labels, and a nonzero
three-bit state with `n` labels among `135,125,225`, the new coefficients
are exactly

| Measure and coordinate | Coefficient |
| --- | --- |
| Raw `X` | `W*h(B+q)` |
| Survivor `Y` | `Phi5(B+q)` |
| Raw marked `U` | `W*(h(B+q+n)-h(B+q))` |
| Survivor marked `V` | `Phi5(B+q+n)-Phi5(B+q)` |

The unchanged marked offsets are `U=876`, `V=3676`. The exact model-row
hash is `9f571ed4977b916e2a0823e5e7262eb333717301ac85a30f6c96671ebc9465ce`.
All these state coefficients are nonnegative. The common-parameter
secant and complete constant are unchanged.

No exponent tail is truncated. The selected old-old pair payment is
`11537/202500` over 21 pairs; its complete complement is
`132479/1620000`. The selected old-positive-seven payment is
`17351/275625` over 49 blocks; its complete complement is
`51501/490000`. Original complete payments remain `111/800`,
`121/720`, and `89/240` for POO, POZ, and PZZ. The entire pure-seven
weight is `1/5`, and the conditional PZZ later-depth constant remains
`31/1470`.

The fixed pruning threshold is the maximum of exactly the same 60
original seed branches. Additional residual certificates do not change
that partition. Every one of the 12500 original layouts and its 5000
independent projection choices is accounted for:

| Region | Count |
| --- | ---: |
| Entire layouts bounded before projection | 12488 |
| Projections bounded by complete conditional affine bounds | 59318 |
| Projections bounded by seed duals | 40 |
| Projections bounded by original seven-label duals | 197 |
| Residual projections with new exact duals | 445 |

Thus `5000*12488+59318+40+197+445=62500000`. The branch-decision digest
is `0d766a8449ae7b7c3d113e8bd0a534028369a70897d6e7275a3aab734b776277`.
Original duals are used only after checking componentwise objective
dominance with the same complete constant, then rechecking every dual
column for the corrected objective. Each residual adopts the minimum of
its new bound and the strongest valid prior bound. The final full bound
is the maximum of the fixed threshold and every residual's adopted bound.

The standalone
[checker](../../frontier/j-source/j_face_exact_seven_retained_factorial_head.py)
reconstructs all original source constraints, the full partition, every
residual, and the exact rational certificate. Its bank has 505 duals,
covering 3298155 new-objective column inequalities; 197 original reused
duals contribute 1286607 further column checks. The
[certificate](../../certificates/source_norms/j-source/j_face_exact_seven_retained_factorial_head.json)
contains no optimizer or scratch-directory dependency. The solver is
used only to propose rational duals.

This is a complete source inequality on the two saturated J faces.
It does not assert source attainment, extension away from those faces,
a global join, Lean verification, or a solution of unrestricted Erdős #7.
The complete 52-cost comparison is a separate consumer.
