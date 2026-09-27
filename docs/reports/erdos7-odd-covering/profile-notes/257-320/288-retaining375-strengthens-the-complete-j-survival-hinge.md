[Index](../../marked_head_profile.md) · [Seven old states](264-seven-retained-states-and-two-seven-depths-control-complete-j-heads.md) · [Eight positive-seven projections](280-second-depth-cofactors-sharpen-the-complete-j-survival-hinge.md)

# Retaining375 strengthens the complete J survival hinge

On both entire actual saturated J faces, the original load A and survivor
measure mu satisfy

    integral(A-4)_+ dmu<=767945288466086119/3969000000000000000
                       ≈0.19348583735603076820.                 (RS1)

The complete improvement over280 is

    10289991277193671/13891500000000000000
      ≈0.000740740112816734766.                                (RS2)

All3,125,000,000 independent original containing choices are covered.
The original264 source constraints and all exponent/cofactor tails
remain. The new information is the actual joint placement of the old
label375 within every retained state and its complement.

## One original event refines all eight old states

For each of264's400 rectangle-mask coordinates and marked state
s=0,...,7, let R_s and S_s be the actual raw and survivor measures.
For s>0 these are264's existing U_s,V_s. For s=0 they are the implicit
complements X-sum U_s and Y-sum V_s. The original constraints give

    R_s>=0, S_s>=0, S_s<=w R_s.

For the independently chosen original event J375, introduce

    a_s=Lambda(state_s intersect J375),
    b_s=mu(state_s intersect J375).

The extension imposes

    0<=a_s<=R_s,    0<=b_s<=S_s,
    b_s<=w a_s,    S_s-b_s<=w(R_s-a_s).                         (RS3)

Both J375 and its complement obey the same survivor density. Every
actual source supplies these variables by taking its own intersections;
no independence or coinciding original residues are assumed.

The label375=3*5^3 has its own ten-coordinate(root,slot) simplex lambda.
At old cell(c,u), the complete raw profile is

    sum_(marked states,masks) a_s
      <=E(c,u)/125 *lambda(ROOT(c),u).                         (RS4)

An actual positive-source event selects its own root and slot. An absent
or source-null event has zero new intersections and may use any point of
the simplex. Mixtures only enlarge the feasible set. The complete global
survivor cap is sum b_s<=1/375. No375 residue is identified with the
existing125 or75 residue.

Generalized CRT gives the additional raw intersection caps

| Other original label |25|27|75|81|135|125|225|
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| LCM with375 |375|3375|375|10125|3375|375|1125|

Each intersection is at most the reciprocal of its LCM; incompatible
residues give an empty intersection. The sums use the appropriate old
mask or marked-state bit, so intersections share the same actual source.

All6531 original variables,11211 inequalities and19 equalities remain
verbatim. The extension adds3200 raw intersections,3200 survivor
intersections and10 profile coordinates. The result has12941 variables,
30454 inequalities and20 equalities. Existing marked deletions and the
single late parameter remain intact.

## The full target and every unretained tail remain

Fix any original shallow layout and all eight independently chosen
positive-seven projections21,35,63,105,147,245,441,735. At a rectangle,
let m count the four first-depth matches and e the four second-depth
matches. The inherited complete raw cap kernel is

    g(v)=(6/35)*(1+m-q)_+
         +(6/245)*(1+e-(q-1-m)_+)_+
         +1/(5*7^(2+(q-2-m-e)_+)),    q=(4-v)_+.               (RS5)

With old mask count h and marked count n_s=popcount(s), write
v=B+h+n_s. Keeping375 adds exactly

    [g(v+1)-g(v)]*a_s
      +[(v+1-4)_+-(v-4)_+]*b_s                                (RS6)

to the existing264 objective with the eight-projection kernel. The
formula applies to all eight states, including the implicit zero state.
The old marked-state terms remain; no state mass is counted twice.

The raw kernel is nondecreasing at its finite transitions and is exactly
constant for every v>=4. The hinge continues with slope1. Consequently
the same original positive-part cap argument applies to every remaining
indicator and to arbitrarily large remaining load.

Only375's own assigned old cap is removed:

    6151/405000-1/375=5071/405000.                              (RS7)

The complete positive-seven tail remains13/490. In particular the
different labels375*7^j, j>=1, are still paid there. The full objective
constant is

    5071/405000+13/490=774979/19845000.                         (RS8)

The full target is still H4(n)=(n-4)_+ on all positive integers. There is
no finite exponent or load cutoff, nor any change to the target threshold.

## Every original choice has an exact bound

The complete280 two/four/six/seven/eight projection affine bounds and
its existing exact duals remain valid. They are compared exactly with a
fixed candidate supplied by one explicit375 seed dual. That seed is not
assumed to control all layouts.

At the value in(RS1), the complete inherited prefix ledger gives

| Stage | Number bounded at this stage |
| --- | ---: |
| Two projections |124994|
| Four projections |295|
| Six projections |46|
| Seven projections |5|
| Eight projections by existing seed duals |46|
| Remaining eight-projection leaves |104|

The exact original-domain identity is

    25000*124994+500*295+50*46+10*5+46+104=3125000000.           (RS9)

Every one of the104 remaining leaves receives a12941-column exact
375 dual. The final bound is

    max(fixed candidate,
        max_(remaining leaves) min(new complete bound,old complete bound)).
                                                               (RS10)

Thus even if a remaining leaf raised the final maximum, every earlier
pruned choice would still be covered. Here the final maximum equals
the fixed candidate, proving(RS1).

The104 distinct duals check1,345,864 columns. The inherited proof also
rechecks50 original280 seed duals,26 available256 duals and600 independent
unscaled affine endpoints. All branch decisions and the104-leaf list
recompute exactly. The existing rational-table/run-length codec is used.

The [helper](../../frontier/j-geometry/j_face_retained375_survival_heads.py) and
[certificate](../../certificates/source_norms/j-geometry/j_face_retained375_survival_heads.json)
replay using exact standard-library arithmetic:

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j-geometry/j_face_retained375_survival_heads.py --check
```

This is a complete source bound on the two saturated actual J faces.
A separate consumer must recompute the52-cost comparison and survival
denominator. Actual-source attainment, off-face extension, global joining,
Lean verification and unrestricted Erdos7 are not conclusions of this result.
