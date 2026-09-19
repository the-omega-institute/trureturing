[Index](../../marked_head_profile.md) · [Complete second-depth heavy bounds](204-a-second-seven-depth-strengthens-both-complete-heavy-costs.md) · [Shared selected-intersection interface](201-two-more-seven-labels-and-selected-intersections-control-both-heavy-costs.md) · [Complete survival denominator](203-the-expanded-seven-head-improves-the-complete-survival-denominator.md)

# Eleven independent original costs use the expanded seven interface

On both whole actual saturated K faces, the complete comparison is

    K <= 2317068337005829417579519355454602747100113/5403859595209570937396996220316137000000
      = 428.78026273293089436407695998166313922... .                                    (LC1)

The improvement over204 is 4.2028272972569200954342514149137187102.... Eleven other original linear
costs benefit from201's common head and selected-intersection bounds.
The result retains204's two heavy bounds and the entire preceding
52-cost vector, complete square and denominator. The sufficient
threshold403 is not reached.

## 1. The interface applies to each complete original function

For each listed original cost f_i, let

    c_i=f_i(1),
    a_i1=f_i(2)-f_i(1),
    a_it=f_i(t+1)-2*f_i(t)+f_i(t-1), 2<=t<=8.

All coefficients a_it are nonnegative. The pinned original function
has an affine continuation starting at a cutoff at most8. Direct
finite evaluation and the two identities

    sum_t a_it = original eventual slope,
    c_i-sum_t t*a_it = original eventual constant

give the complete identity

    f_i(v)=c_i+sum_(t=1..8)a_it*(v-t)_+, v>=1.       (LC2)

This is an identity on all positive integer loads. Matching only a
finite sample would not suffice; the full affine tail is also matched.
The exact functions, count weights and original AP block indices are
read from the unchanged original inventory.

Apply201(EP14) to the nonnegative combination in(LC2). The same head,
21/35/63/105 projections and selected25/27/75/81 events are retained
through all thresholds of this one cost. In particular the mean-head
correction is -a_i1*C(layout), inside the same head maximum. The
positive-seven tail13/360 and each complete zero-seven remainder
stay in the objective. All selected intersections retain the same
actual raw source, with their CRT caps1/675 and1/2025.

Every cost has its own original test, independent residues and source
maximum. Uniform inequalities may be added with their original positive
weights against the common actual survivor measure; this makes no
claim that the maximizing heads coincide or are jointly attained.
The constant c_i integrates against the exact survivor mass53/360.

The complete resulting bounds are:

| Original index | Complete cost upper | Weighted numerator decrease |
| ---: | ---: | ---: |
| 1 | 5769426295870866157/3867313776060735000 | 0.0664950610175748 |
| 2 | 24567455219148893/150674562703665000 | 0.0011404383475389 |
| 7 | 33963087014627506721/19983303008741872800 | 0.0764293550270783 |
| 10 | 2957960094980447/13444698144477600 | 0.0015604495008928 |
| 17 | 14150363320365198917/11865621812913618750 | 0.0469777420427952 |
| 18 | 31569249404242003/242155547202318750 | 0.0008067383035863 |
| 23 | 10079138795402167804591/7418801241995420277000 | 0.0539967079021910 |
| 26 | 14340987959142757181/81525288373576047000 | 0.0011038513269035 |
| 32 | 388975899088654/2033112158102025 | 0.0962567877474740 |
| 33 | 25334451641/571516320375 | 0.0021855634561516 |
| 36 | 5974997801/117847341612 | 0.0025304086280977 |

For each cost201's scanner covers all125000 original head/21/35
branches and all50 additional63/105 projections when needed. An
unexpanded branch is covered by a valid old upper no larger than
the final maximum. The eleven scans check 1383660 exact rational
LPs in total and retain their branch digests and full containing
inventories. Each invoked LP has matching feasible primal and dual
values. No exponent tail is replaced by a finite-height experiment.

## 2. One complete numerator retains every previous improvement

Use the original52 positive cost weights. Keep the signed mass
coefficient, exact mass D=53/360, and the complete-square term with
Q=8201/1800. Replace the eleven bounds by(LC2)'s integrated values,
retaining every previous bound as an available option. The existing
whole-integer majorant propagation adds no further improvement in
this substitution: exactly the eleven listed indices change.

Thus the full numerator decreases by

    8392493064190498544699812523
      /24014016657564869166891660000

and becomes

    N <= 7613760202753326767418980271659178189317/224864850579771678391856815074000000000.                                   (LC3)

The two204 heavy costs, the other original costs,202's eight all-load
identities, and203's fourth-hinge feedback are all retained. This is
one complete vector evaluation, not a sum of decrements obtained
using incompatible denominators or numerator vectors.

The denominator remains exactly203's positive lower bound

    d >=1420639249067/17084377926000.

It retains all four independently maximized AP11 blocks, the separate
AP13 fourth hinge and the whole infinite-count remainder3337/52707600.
Together with the original offset185694867601/8599322160, (LC3)
gives(LC1).

The [helper](../../frontier/transport/expanded_seven_linear_comparison.py) and
[certificate](../../certificates/source_norms/expanded_seven_linear_comparison.json)
retain all complete function identities, eleven independent source
scans, the full cost vector and the full denominator.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/transport/expanded_seven_linear_comparison.py --check
```

These are ordinary source inequalities and exact rational checks on
the two stated saturated faces. No off-face or global improvement,
Lean verification, actual simultaneous attainment or unrestricted
Erdos7 resolution is asserted.
