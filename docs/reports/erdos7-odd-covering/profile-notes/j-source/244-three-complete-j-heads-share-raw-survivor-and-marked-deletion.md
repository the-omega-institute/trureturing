[Index](../../marked_head_profile.md) · [Original complete J heads](219-one-late-source-split-controls-complete-saturated-j-heads.md) · [Selected-label peeling](../transport/211-all-four-selected-labels-can-be-retained-above-the-first-hinge.md) · [Marked deep-five deletion](../transport/222-deep-five-deletion-retains-the-selected-observation-masks.md)

# Three complete J heads share raw, survivor and marked deletion

On both entire saturated actual J faces, the complete independent
AP13 and original heavy-cost bounds are

| Original target | Complete upper bound |
| --- | ---: |
|AP13, integral of(A-4)_+|0.196328294280874964...|
|cost0|6.009969384412894581...|
|cost16|4.802983468473917584...|

Each bound covers all6,250,000 original containing choices and
the full late-split interval. They improve219's corresponding
complete bounds0.200564625850340136...,6.075990627615473564...
and4.855722585417471525..., respectively. Every original selected
label, independent projection and complete omitted-label tail
remains present.

The new comparison uses one raw source, one actual survivor and
two projected deletion measures in the same linear program.
Ten necessary marked-event inequalities prevent selected raw
mass and actual deletion from being optimized independently.
The mathematical domain is unchanged from219; no K-domain
numerical bound or forced27 condition is imported.

These are three complete head bounds. They are not a complete
52-cost comparison, an off-face extension, an assertion of actual
LP attainment, a Lean verification or an unrestricted Erdos7 result.

## 1. Original J geometry and one common late coordinate

Use219's canonical five ternary cells c=0,...,4 and five quinary
slots(P,A,B,Q,H), with

    ROOT=(0,0,1,1,1),
    eta=(1/18,1/9,1/9,1/9,1/9),
    q=(0,1/5,1/5,3/20,1/5).

The raw source Lambda has mass1/4 and the actual survivor mu
has mass3/20. Its three raw group budgets are1/24,1/12,1/8.
The late parameter obeys

    theta=1/135+(1/270)*x,  0<=x<=1.                 (JJ1)

Only the raw caps of(cell3,B) and(cell4,B) vary with x. Their
rows have coefficients+1/270 and-1/270, respectively, on the
left side. Thus one scalar x controls both opposing movements;
they are not maximized at unrelated late parameters.

Write p_(c,s) for219's normalized deep-ternary coefficients,
E_(c,s) for its absolute descendant-five coefficients, and
w_(c,s) for its retained survivor density. The distinction
between p and the absolute raw cap is retained: the selected
27 and81 profiles use p/27 and p/81, not a raw cap in their place.
The geometry record agrees exactly with219, including both faces
and all transported source-cell permutations.

## 2. One876-variable necessary relaxation

Split every cell-slot rectangle by the16 masks m of the four
independent original selected events25,27,75,81. Let

    X_(c,s,m)=Lambda(rectangle(c,s) intersect mask m),
    Y_(c,s,m)=mu(rectangle(c,s) intersect mask m).      (JJ2)

There are400 raw variables X,400 survivor variables Y,25
projection weights lambda,25 variables e3,25 variables e5 and
the one normalized late coordinate x. All876 variables are
nonnegative. The projection simplexes have sizes5,5,10,5.

For each original selected event, its actual projection is a
point mass in its own simplex. Mixtures enlarge the feasible set;
they neither identify independent residues nor assert that every
mixture is realizable. The original425-variable raw model supplies
the25 rectangle caps, three group budgets,100 selected-profile
inequalities and four intersection caps. The profiles are

    25: E_(c,s)/25, supported at its own slot;
    27: p_(c,s)/27, supported at its own parent cell;
    75: E_(c,s)/25, supported at its own root and slot;
    81: p_(c,s)/81, supported at its own parent cell.  (JJ3)

The two mixed27 intersections have cap1/675, and the two
mixed81 intersections have cap1/2025. The source and survivor
constraints include

    sum X=1/4,  sum Y=3/20,  Y_(c,s,m)<=w_(c,s)*X_(c,s,m),
    selected Y totals <=(13/750,11/540,1/75,11/1620). (JJ4)

Let E3 be the complete projected forbidden deep-three deletion,
and E5 the complete projected pure-five-deep plus root1-five-deep
deletion. Their original label families are distinct from each
other and from the shallow deletions already incorporated into w.
Saturation identifies actual deletion with the sum of its virtual
label deletions, giving the measure inequality

    E3+E5 <= w*Lambda-mu.                             (JJ5)

Its rectangle marginals therefore satisfy

    e3_(c,s)+e5_(c,s) <= sum_m(w_(c,s)*X_(c,s,m)-Y_(c,s,m)),
    e3_(c,s)=0 for c>=2,
    sum_(c=0,1)e3_(c,s)=q_s/90,
    sum_s e5_(c,s)=eta_c*(1+ROOT(c))/100=:M_c.         (JJ6)

These are the complete J deletion marginals, not a chosen finite
height truncation. No K-specific lower bound in cell1 is imposed.

Absent and source-null selected events use the following projection
conventions:25 chooses P;75 chooses(root0,P);27 and81 choose
cell0. Their raw and survivor event masses are zero. The added
marked lower bounds below then have zero right sides, so every
such original case remains included in the relaxation.

## 3. Ten marked residual inequalities retain common deletion

Define the residual of selected event j in cell c by

    D_j(c)=sum_(s,m:j in m)(w_(c,s)*X_(c,s,m)-Y_(c,s,m)).

The same cap-equality argument as222's(DM1)--(DM2) applies to
the J source: complete deep-five deletion factors as

    E5=eta tensor nu_p+(eta restricted to root1) tensor nu_a,
    nu_p(1)=nu_a(1)=1/100.                            (JJ7)

On cells c=1,...,4 the ternary measure is unthinned Haar. The
original27 and81 subcylinders therefore occupy respectively1/3
and1/9 of the E5 cell marginal. Since the selected residual
dominates its actual E5 mass, every actual configuration obeys

    D_27(c) >= (M_c/3)*lambda27(c),
    D_81(c) >= (M_c/9)*lambda81(c), c=1,...,4.        (JJ8)

No such ratio is imposed in the thinned cell0. Each inequality
is linear in the original projection coordinates and so remains
a necessary constraint when the point masses are relaxed.

Likewise deep-three cap equality gives

    E3=nu3 tensor q,  nu3(root0)=1/90.               (JJ9)

On each of the source-free slots A,B,H, an original25 cylinder
selects one fifth of the slot; the same holds for a75 cylinder
whose root is0. Hence

    sum_c D_25(c) >= [lambda25(A)+lambda25(B)+lambda25(H)]/2250,
    sum_c D_75(c) >= [lambda75(0,A)+lambda75(0,B)+lambda75(0,H)]/2250.
                                                               (JJ10)

Q contributes a nonnegative quantity that these two inequalities
discard. The eight rows(JJ8) and two rows(JJ10) all concern the
same residual masses from(JJ2). Different selected events can
overlap: their deletion charges are not added as if disjoint.

The resulting necessary LP has587 inequalities and16 equalities.
It is only a relaxation of the actual source family. Its feasible
points and maximizing dual branches are not asserted realizable.

## 4. Retained survivor hinges and raw seven increments

For every independently chosen original shallow head put

    B=1+I3+I9+I5+I15+I45.

Retain the four independent positive-seven projections21,35,63,
105, and let ell_(c,s) count their selected indicators. At threshold
t use

    v_t(c,s,m)=B_(c,s)                 if t=1,
    v_t(c,s,m)=B_(c,s)+popcount(m)     if t>=2.        (JJ11)

This is211's all-selected peeling policy with219's J cap series
and positive-seven bridge. For nonnegative rational coefficients
a_t, the LP objective is

    sum_(c,s,m,t) a_t *[
      Y_(c,s,m)*(v_t(c,s,m)-t)_+
      +X_(c,s,m)*g_t(v_t(c,s,m),ell_(c,s))].         (JJ12)

The old hinge uses the actual survivor Y; the seven increment g
uses the same raw source X. The deletion constraints already
control their difference, so no e3/e5 correction is subtracted
again outside(JJ12).

The complete remaining cap contribution is exactly

    a_1*(R0+Z4)+sum_(t>=2)a_t*(R4+Z4),
    R0=53/600, R4=2471/81000, Z4=1/28.              (JJ13)

Every selected old label is either retained in(JJ11) or paid in
its assigned remainder. Every positive-seven label is either in
the bridge or paid in Z4. The remainder sums include all exponent
heights. The heavy targets use their unchanged original hinge
coefficients and separate constant f(1)*3/20; here f(1)=0.

## 5. Complete enumeration and rational dual replay

Each target has12,500 original shallow layouts,10 choices of
the21/35 projections and50 choices of the63/105 projections:
6,250,000 containing choices in total. The LP itself includes all
four selected25/27/75/81 projection choices through their separate
simplexes and includes the entire theta interval in one model.

The complete219 bounds provide safe pruning. A two-projection
branch uses the maximum of its affine endpoint values. A remaining
four-projection branch uses the exact maximum over x in[0,1] of
the minimum of the two complete affine bounds; both endpoints
and every strict interior crossing are checked. For an unpruned
branch, take the minimum of that old complete bound and the new
feasible-dual value plus(JJ13). The maximum over all branches
is the reported uniform result.

| Target | Two-projection branches | Pruned there | Expanded four-projection branches | New LP branches |
| --- | ---: | ---: | ---: | ---: |
|AP13|125000|124997|150|4|
|cost0|125000|123244|87800|7|
|cost16|125000|123223|88850|9|

In each row,50 times the pruned-two count plus the expanded-four
count equals6,250,000. The expanded-four branches not using the
new LP are bounded by the complete old affine pair. A previously
certified maximizing branch supplies an additional seed evaluation;
its dual is reused when the enumeration reaches it. All three
targets together retain20 distinct duals and18,750,000 containing
choices. The original affine compiler is independently checked
against unscaled Fraction evaluations42 times in total.

For the LP A z<=b,E z=e,z>=0, every stored dual has y>=0 and
free equality multiplier h, and satisfies

    A^T*y+E^T*h >= objective                         (JJ14)

in all876 columns. The resulting upper is b^T*y+e^T*h. All20
records are checked exactly, giving17,520 rational column checks.
Each key binds the regenerated objective and full model matrix;
the default checker also redoes the entire pruning enumeration
and reconstructs every certificate field.

The canonical verifier uses only the Python standard library.
Numerical optimization is confined to the separate proposal tool;
its proposed multipliers are rationalized, repaired and accepted
only after(JJ14) passes exactly. No numerical solver status is a
proof of the claimed bound.

## 6. Artifacts and remaining boundary

- [Complete J joint-head verifier](../../frontier/j-source/j_face_joint_selected_heads.py)
- [Optional numerical proposal tool](../../frontier/propose_j_face_joint_selected_heads.py)
- [Rational dual bank and complete scan certificate](../../certificates/source_norms/j-source/j_face_joint_selected_heads.json)

The new information is the simultaneous raw/survivor/deletion
constraint, including marked selected events. It is compatible
with the same-domain complete square and linear-head inputs,
but assembling a new52-cost comparison remains a separate
consumer obligation. No unmeasured joint attainment of independent
original costs is inferred from their separate upper bounds.
