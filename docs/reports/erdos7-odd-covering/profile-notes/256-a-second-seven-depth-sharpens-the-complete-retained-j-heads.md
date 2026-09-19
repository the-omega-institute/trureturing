[Index](../marked_head_profile.md) · [Same retained J source](251-two-retained-original-tests-sharpen-the-complete-j-heads.md) · [General two-depth bridge](204-a-second-seven-depth-strengthens-both-complete-heavy-costs.md) · [Original J profiles and complete caps](219-one-late-source-split-controls-complete-saturated-j-heads.md)

# A second seven depth sharpens the complete retained J heads

On both entire actual saturated J faces, the independently chosen original
labels147 and245 can enter the retained bridge on251's unchanged source
model. The resulting complete original-function bounds are:

| Original function | Previous complete upper | New complete upper |
| --- | ---: | ---: |
| AP13 | 0.194906849653694321563546053... | 0.194906849629635927257675556... |
| 0 | 5.694565687831699609719876961... | 5.614947195860340363802219458... |
| 16 | 4.550682696982637133600824798... | 4.486692197855258203297416668... |

Each target covers all62,500,000 original containing choices, the whole
late-split interval and complete exponent tails. The same3306-variable
actual raw/survivor model retains the two original labels135 and125, all
marked deletion constraints and independent original test residues.

The exact new complete bounds, in the displayed order, are

    5415097003260174967/27783000000000000000,
    441646680424072921714465863120862026017/78655535843628247939685250000000000000,
    81520634346165968291365147795240273044149/18169428779878125274067292750000000000000,

The AP13 difference is only

    95487767/3969000000000000000,

which is less than1/10^10. This small exact certificate improvement is
reported separately from the larger heavy-cost gains; no LP attainment
or additional structural AP13 gap is inferred.

## Two additional original projections, on the same source

Retain251's actual raw source Lambda, actual survivor mu,25-rectangle/16-mask
partition, four135/125 membership states and all3306 nonnegative variables.
The6354 inequalities and18 equalities are unchanged. In particular, both
old marked deletion families, their ten residual constraints and the common
late parameter theta in[1/135,1/90] remain inside the same model.

At an old rectangle(c,s), the four existing independent original projections
21,35,63,105 give

    m=I_(ROOT(c)=r21)+I_(s=s35)+I_(c=c63)
                         +I_(ROOT(c)=r105,s=s105).

Add the independent original projections147=3*7^2 and245=5*7^2:

    e=I_(ROOT(c)=r147)+I_(s=s245), 0<=e<=2.          (JD1)

Neither new residue is identified with its depth-one counterpart. There
are ten choices(r147,s245), all included. A source-null or absent147
projection contributes zero and may be dominated by a live-root projection;
the bridge increases with its indicator count. The same completion applies
to an absent245 label. This introduces only containing upper configurations,
not an assertion that every completed family is actually realized. The
finite old observation still
only requires the same25 rectangles; no new restriction on the source is
imposed by retaining these two projections.

## The entire two-depth seven bridge

For a fixed old point, the retained positive-seven list has1+m labels at
depth one,1+e labels at depth two, and the original unit7^k label at every
k>=3. The normalized raw cap of each depth-k indicator is6/(5*7^k).
Order the finite depth-one group first, the depth-two group second, then
all remaining unit powers.

For a nonnegative integer q, the sum of the first q indicators is at most q
pointwise.
Consequently the positive part of the retained count minus q is at most
the remaining indicator sum. This does not require any nesting or matching
of the original seven residues. The complete remaining cap series is

    G_(m,e)(q)=(6/35)*(1+m-q)_+
      +(6/245)*(1+e-(q-1-m)_+)_+
      +1/[5*7^(2+(q-2-m-e)_+)].                    (JD2)

The geometric term contains every remaining unit power. Define

    g_(t,m,e)(v)=G_(m,e)((t-v)_+).

For e=0 this equals251's complete one-depth bridge exactly. The identity
is algebraic: group the single second-depth unit with the remaining
geometric series. We reuse204's general arbitrary-residue formula; its
K-specific source caps and numerical inequalities are not inputs here.

For a retained density w, the function

    f_t(v)=w*(v-t)_+ +g_(t,m,e)(v)

is increasing and integer-convex. Before v reaches t, its increments read
the ordered cap list in reverse and are nondecreasing. Above the threshold
its increment is w>=2/5>6/35, and the raw increment is constant. The helper
checks all finite transitions for t=1,...,8, all J density weights,
0<=m<=4,0<=e<=2 and old loads through13, along with this exact affine
continuation. Thus no large-load or large-exponent cutoff is assumed.

## The J tail removes its own two assigned labels

The complete J four-projection tail in219/251 is Z4=1/28. The original
J raw old-cofactor caps for3 and5 are1/8 and1/10. Their designated terms
at the second seven depth are therefore

    cap147=(6/245)*(1/8)=3/980,
    cap245=(6/245)*(1/10)=3/1225.

Both are actual assigned summands of the same complete nonnegative
cap series. Moving precisely those labels into the retained bridge gives

    Z6=1/28-3/980-3/1225=37/1225>0.                 (JD3)

This is a partition of a complete cap series, not subtraction of upper
estimates from unknown actual mass. The zero-seven tails are exactly251's:
R0=53/600 for t=1 and Rpair=7951/405000 for t>=2. Hence the complete
external payment for coefficients a_t>=0 is

    a1*(53/600+37/1225)
       +sum_(t>=2)a_t*(7951/405000+37/1225).        (JD4)

Every old or positive-seven label is retained or paid once, and every
infinite exponent tail remains included.

## The same four-state raw/survivor objective

Write B=1+I3+I9+I5+I15+I45 and v=B+popcount(mask). The old actual raw
mass X carries g; the actual survivor mass Y carries the old hinge.
For thresholds t>=2,251's three explicit states add n_i=1,1,2 to v.
Their complete objective, with the neither-state implicit, is

    sum_(cells,masks,t)a_t*[X*g_t(v_t)+Y*(v_t-t)_+]
      +sum_(cells,masks,i,t>=2)a_t*[
          u_i*(g_t(v+n_i)-g_t(v))
          +v_i*((v+n_i-t)_+-(v-t)_+)],              (JD5)

where v_1=B and v_t=v for t>=2; the g in(JD5) is(JD2) with that
rectangle's first- and second-depth counts. Add(JD4) to obtain the
complete head bound.

All state masses come from251's same actual four-way partition. Its
complement domination, independent135/125 profiles, J-specific125 cap,
raw CRT intersections and whole late interval are retained verbatim.
Only the objective and designated positive-seven tail change. The
same3306-column rational dual checker therefore applies without any
additional source premise. No deletion credit is added outside(JD5).

## Complete affine bounds supply valid uniform pruning

The complete two- and four-projection affine bounds from219 still apply
to each original full load. A third complete affine bound uses(JD2) with
219's original selected prefixes k_t=min(t-1,4), the same normalized
ternary operators, absolute five operators, original raw intersection
bounds, raw source capacity and complete deletion correction.

This third bound has its own complete external payment

    sum_t a_t*(R_(k_t)+Z6),                         (JD6)

with219's unchanged(R0,...,R4). It need not use the larger retained set
in(JD5): each is an independently complete upper for the same original
function, so their minimum is valid. In particular, tails from one
partition are never combined with retained gains from another.

Only the raw source capacity depends on theta; all other terms are
constant. Thus the three bounds are affine functions on one common
interval. The maximum of their lower envelope occurs at an endpoint
or a pairwise line intersection inside the interval. The scanner checks
both endpoints and every such exact intersection, including distinct
interior candidates even when an intersection is not active in the
lower envelope. Independent unscaled rational evaluations check the
new affine compiler and its maximizing branches.

A251 dual is reused only when the full regenerated old objective hash
matches. Its complete3306-column inequalities are verified before use;
its bound controls all ten new projections. Every newly proposed dual
is likewise checked with exact integer arithmetic after clearing positive
denominators. Numerical optimization supplies candidate prices only.

## Every original choice and tail is covered

Each target has12,500 original shallow layouts, ten independent21/35
choices,50 independent63/105 choices and ten independent147/245 choices:
62,500,000 original containing branches. The two original135/125 tests
remain independently represented by the same profile variables at every
branch. The source LP covers the entire late interval jointly.

A complete two-projection upper can bound500 containing branches at once;
a complete four-projection or identical251 upper can bound ten. For each
remaining branch, the exact three-affine upper and the new complete joint
source dual give further bounds. A branch is pruned only when its whole
upper is no larger than the current certified scan maximum, which never
decreases. The exact accounting identity is

    500*two_bounded+10*(four_bounded+prior251_bounded)
                   +six_projection_branches=62,500,000,

    six_affine_bounded+joint_dual_branches
                   =six_projection_branches.       (JD7)

The certificate keeps these complete partitions, branch-decision digests,
maximal pruned values and maximizing certificate branches. Such a branch
identifies the largest retained upper in this calculation; it is not a
claim that an actual family attains a containing LP optimum.

## Exact complete scan inventory

| Target | Two branches | Pruned two | Four branches | Pruned four | Prior251 prune | Six branches | Six affine prune | Joint dual branches |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| AP13 | 125000 | 124994 | 300 | 296 | 0 | 40 | 14 | 26 |
| 0 | 125000 | 85028 | 1998600 | 1998106 | 149 | 3450 | 3149 | 301 |
| 16 | 125000 | 84348 | 2032600 | 2032102 | 158 | 3400 | 3097 | 303 |

The complete three-target inventory contains187,500,000 original choices.
All630 distinct new duals are consumed, with all2082780 rational column
inequalities checked. The complete affine compilation and maximizing
branch checks additionally contain57 independent unscaled readings.
The certificate stores every inequality price, unrestricted equality
price and signed objective value in the existing lossless rational-table
and run-length codec. Decode-to-original equality is checked before
publication, and the canonical verifier decodes before exact validation.

## Actual-source transport and scope

The source relabelling from130/219/251 transports the whole raw source,
survivor, old and new profiles, four membership states and six independent
seven projections to the second J orientation and all admissible source
permutations. The two additional finite cylinder observations also pass
through the existing labelwise diagonal construction, while the complete
geometric tails remain uniform.

The [helper](../frontier/j_face_second_depth_retained_heads.py),
[certificate](../certificates/source_norms/j_face_second_depth_retained_heads.json)
and [optional proposer](../frontier/propose_j_face_second_depth_retained_heads.py)
retain the exact source pins, unchanged model, complete objectives,
losslessly encoded rational duals and all original branch choices.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j_face_second_depth_retained_heads.py --check
```

These are ordinary complete source inequalities on both entire saturated
actual J faces. They do not establish an off-face neighborhood, a new
full52-cost numerator/denominator ratio, Lean verification or an
unrestricted Erdos7 resolution.
