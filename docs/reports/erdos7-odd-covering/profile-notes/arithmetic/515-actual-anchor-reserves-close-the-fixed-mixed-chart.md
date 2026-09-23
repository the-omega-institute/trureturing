# Actual anchor reserves close the fixed mixed split/common chart

The fixed completed chart of
[report509](509-finite-height-zero-edges-strengthen-the-global-support-bound.md)
cannot support a covering. All561 legal choices of the selected45/75
classes are excluded, with same-source comparison margin at least

    delta=0.00003940099184888167...>1/26000.                (A1)

The exact minimum is retained in the result JSON. This is a separation
between a source mass lower bound and an exact-zero source mass upper
bound. It is not a height-independent Haar survival bound.

The result concerns the normalized source type(2,4,1), the later3/5
reference paths(2,7,3,4), split coordinates3,5,7, common queried prefixes
at11,13,17,19, and later coordinates23,29. Each original later numerical
label d*23^j*29^k, j+k>0, has one fixed selector between the two global
old references. Old-only phases are arbitrary subject to this completed
chart; they are not required to choose one of those references. Original
finite heights and new-coordinate residues remain arbitrary.

These are ordinary mathematical deductions and exact rational
certificates. No new Lean verification, unrestricted Erdős#7 conclusion,
other reference chart or other split/common pattern is claimed. The source
construction remains Michael Schroeder's *Nine Prime Divisors in Odd
Distinct Covering Systems*, edition1.0.1, with attribution and the local
arbitrary-height verification boundary in the
[library entry](../../../../../Library/Arith/schroeder2026nine.md).

## One source, with a reserve attached to its actual phases

Use exactly the completed-and-charged source nu of
[reports466](466-randomized-completion-retains-full-original-survivor-support.md)
and[467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md),
for one fixed legal completion and one fixed charged choice. The conditional
caps at7,11,13,17,19 are(3/2,5/3,3/2,2,9/5), and its existing mass lower is

    m7=7235955529/450000000000=0.01607990117555555... .    (A2)

Its selected shallow classes are

    0 mod3,1 mod9,4 mod27,0 mod5,1 mod25,2 mod15.

Let A6 be their complement modulo675; it contains221 cells. As in
[report493](493-retained-shallow-anchors-leave-the-pair-obstruction.md),
the selected45/75 phases have exactly the domains

    F45={r mod45:r%3!=0,r%9!=1,r%5!=0,r%15!=2},
    F75={s mod75:s%3!=0,s%5!=0,s%25!=1,s%15!=2}.          (A3)

There are17 and33 choices. Fix(r,s) once and define

    A8(r,s)=A6 minus(C45(r) union C75(s)),
    n45(r)=#(A6 intersect C45(r)),
    n75(s)=#(A6 intersect C75(s)),
    c(r,s)=1/45-n45(r)/675+1/75-n75(s)/675.              (A4)

The same actual source has the stronger lower bound

    nu(1)>=m7+c(r,s).                                  (A5)

To prove it, let P be the product of the completed pure3 and pure5
survivor sets. Disjoint pure-power completion gives H(P)=3/8. The total
reciprocal inventory of mixed labels3^i*5^j, i,j>=1, is1/8. The basic
reserve in Chapter31, (SV19), subtracts this full inventory and restores
only the already deleted part of the selected15 class. In135-cell units
the worst type has

    R=135/4+9D2,

where D2 is the relative pure5 deletion in root2. It contains no45 or75
credit. Each such mixed label was charged its own full1/m.

Both legal45/75 cylinders avoid the selected15 class. Consequently

    P intersect C45(r) subset A6 intersect C45(r),
    P intersect C75(s) subset A6 intersect C75(s).

Replace their two separate1/m charges by these smaller upper bounds on
their actual contribution inside P. This refunds precisely c(r,s).
Physical overlap between the refunded regions does not invalidate the
sum: each refund reduces a distinct term of the original union bound.
This is also not a second refund for15.

All ordinary stage-loss upper bounds at7 through19 remain valid: they
already enlarge the actual initial chart, releasing the45/75 exclusions.
Report467 proves these bounds for the same charged process. For fixed
(r,s), c(r,s) does not depend on the continuous deeper pure5 budget.
Adding it preserves the affine reserve and convex upper-loss comparison
at the same four vertices. Taking their existing minimum therefore gives
A5. No source law or vertex is selected separately for a later query.

For example, at(r,s)=(31,16), n45=8 and n75=5, so c=11/675. The six-anchor
global upper was difficult at that phase pair partly because it had
discarded precisely this phase-dependent source reserve.

CRT intersection calculations also give the explicit credits

    c45(r)=1_{r=4 mod9}/135+1_{r=1 mod5}/225
             -1_{r=4 mod9 and r=1 mod5}/675,
    c75(s)=(4/675)1_{s=1 mod3},
    c(r,s)=c45(r)+c75(s).                               (A5a)

The consumer checks these formulas against the literal cell counts.

## An upper bound for every possible zero support

Retain report509's labelled-box support and all its valid row types:
theta-valid pairs, genuine triples, binary triangle cliques, genuine
four-point rows, finite-height zero-only pairs, mixed cliques and upward
order. These rows concern common original labels and do not depend on
which legal45/75 phases are used in the initial measure.

Let eta_(r,s) be the product of Haar restricted to the joint chart A8(r,s)
and the original split7/common11/13/17/19 comparison laws. Reverse
integration gives

    nu({x: later-fibre survival s(x)=0})
       <=eta_(r,s)(Z),                                 (A6)

where Z is the upward support generated by actual zero-survival old
points. Its Q<=19 coordinates vanish. The full mass with Q>=39 is charged
on the upper side, including every infinite valuation tail.

There are23408 finite profiles with Q<=38 and20076 middle profiles with
20<=Q<=38. Write w_i(r,s) for a middle weight and

    overflow(r,s)=H(A8(r,s))
                  -sum_(all23408 profiles) eta_(r,s)(profile).

For any nonnegative rational prices y on the existing valid rows Az<=b,
the exact signed-dual inequality is

    eta_(r,s)(Z)
       <=overflow(r,s)+y dot b
          +sum_i max(w_i(r,s)-(A^T y)_i,0).             (A7)

Order rows contribute a positive parent and a negative child before
taking the positive part. A7 bounds every support satisfying these rows;
it does not just reweight the particular support from report493.

Using report509's original prices,374 of561 pairs have upper<m7. Using
the stronger same-phase lower m7+c(r,s),545 pairs have strict separation.
The remaining16 have c=0 and are exactly

    r in{14,44},
    s in{11,41,56,71} or{14,44,59,74}.                 (A8)

Their complete initial profile weights, together with their total masses,
form two types. The first eight equal those at(14,11), the second eight
equal those at(14,14). Equality holds for all1548 finite3/5 shell pairs,
not merely for total initial mass. It therefore identifies all middle
weights and the full overflow used in A7.

For these two types, use the accompanying rational price certificates
on the same existing row set. All prices have denominator10^14.

| Representative | Active prices | Exact upper, decimal display | m7 minus upper |
| --- | ---: | ---: | ---: |
| (14,11) | 10024 | 0.016040500183706674... | 0.00003940099184888167... |
| (14,14) | 10028 | 0.015996055092896408... | 0.00008384608265914919... |

The certificate does not require optimal prices or a feasible support
from a solver. Each price names an already validated report509 row;
direct rational evaluation of A7 proves the displayed upper. Across all
561 phase pairs, the least final separation is A1.

## Consequence and boundary

If the original finite family covered every integer, then every actual
old-only survivor in the source would have zero later-fibre survival.
Completion only enlarges the old forbidden union and leaves the original
later classes and selectors fixed. Thus

    m7+c(r,s)<=nu(1)=nu({s=0})<=upper(r,s),

contradicting the strict separation proved for its one actual global
phase pair. This closes the fixed chart for every legal45/75 completion,
including arbitrary charged choices and arbitrary finite later heights.

Report509 uses some qualitative exclusions whose quantitative margins
depend on the finite heights. Therefore A1 alone supplies no uniform
Haar lower bound for the original family, and it is not inserted into a
large-prime tail argument. Other3/5 reference charts, other split/common
patterns, and unrestricted old phases of later labels remain separate
obligations. In particular the unrestricted problem is still open here.

The four-projection comparison of
[report513](513-charged-shallow-deletions-lower-the-actual-source-upper-bound.md)
remains valid. A1 uses the ordinary7 comparison and does not subtract
that additional credit; the reserve and actual45/75 upper weights already
suffice for this fixed chart.

## Reproduction and verification scope

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/actual_anchor_zero_support_closure.py

The standard-library consumer pins the source mass/caps, the four basic
reserve vertices and report509's exact row certificate. It reconstructs
literal CRT cells, all finite profile weights, the complete overflow,
all561 global phases and both new signed price evaluations. By default it
compares with the adjacent result JSON; --output PATH writes that result.
The separate price certificate contains no optimizer dependency.

An independent computation using a Cartesian27-by25 initial chart and
clipped residual savings reproduced all561 bounds and both representative
certificates, including their43 and37 negative signed loads. The source
reserve argument and same-law continuation were reviewed separately.
These checks reuse report509's row validity and the attributed source
construction; they do not rerun the old geometry, establish literature
priority or constitute Lean verification.
