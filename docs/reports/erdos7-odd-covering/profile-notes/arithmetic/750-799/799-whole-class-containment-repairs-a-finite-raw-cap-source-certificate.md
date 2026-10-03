# Removing contained originals repairs a finite raw-cap source certificate

Deleting whole original classes that are contained in retained originals
reduces a concrete2950-label family to51 labels while preserving its exact
covered union. Recomputing the same raw-cap certificate at the fixed weight

    w=(1/3,1/3,1/9,1/9,1/9)

changes failure into success:

| Literal inventory | Raw clipped source certificate | Required mass |
| --- | ---: | ---: |
|2950 original classes |0.022205419703305695...|0.03387749834384971...|
|51 retained classes, same covered union |0.49097680418306305...|0.03387749834384971...|

Both calculations use the actual tight pure-coordinate cylinder constants
and only the raw cap sums of the listed originals. No unused inventory
budget is filled. Before removing contained classes, the exact method gap is

    F_raw=0.022205419703305695...,
    T=0.03387749834384971...,
    T-F_raw=0.011672078640544018...>1/100.                (R1)

Here F_raw is this particular clipped lower certificate for one source
mass. It is not the actual source mass, and its small value is not an
upper bound on survivors. T is the mass required by the existing full-query
product-hinge comparison to certify query cost strictly below28. Thus(R1)
shows a limitation of applying this specified certificate directly to the
unreduced inventory. Whole-class containment supplies a sufficient repair
for this example. The corrected certificate also gives a complete normalized
query-cost upper bound8.100615846719924...<28. The pure reference law, caps,
weights and hinge comparison stay fixed; the thinned internal source is
reconstructed and need not be the same submeasure before and after pruning.

The family has an explicit CRT survivor, verified against every original.
It is consequently a method example, not a covering system or a difficult
instance of unrestricted Erdős#7. The result uses ordinary finite mathematics
and rational computation; no new Lean verification is claimed.

## 1. One explicit finite original inventory

Fix

    Q=(5,7,11,13,17,19,23),   N=1000000,   K=3.

Begin with the originals0 mod3 and1 mod9. The five surviving9-leaves in
the existing two-plus-three order are

    (4,7,2,5,8).

For each q in Q include the three pure originals

    q^(j-1) mod q^j,   j=1,2,3.                        (R2)

There are988 nonunit Q-smooth integers n<=N. For each, include one3n
original and one9n original. Their live root and leaf are the roles of
[Report798's repaired B numerical-slot assignment](798-whole-numerical-slot-completions-retain-a-fixed-law-certificate-obstruction.md), truncated at this
numerical N. Each full original's nonternary residue is2 modn. CRT gives
its single phase: for ternary modulus a in{3,9} and specified ternary
residue t,

    phase=2+n[((t-2)n^(-1)) mod a].                    (R3)

For each of the951 such n with at least two support primes, also include
the no3 original2 modn. The other37 n have singleton support and do not
supply additional no3 originals: the pure inventory is exactly(R2).

The complete inventory counts are

| Inventory | Original labels |
| --- | ---: |
| Pure3 and9 |2|
| Pure nonternary powers |21|
|3n originals |988|
|9n originals |988|
| Mixed no3 originals |951|
| Total |2950|

The [finite certificate](../../../frontier/cover-geometry/refined-capped-source/raw_finite_slot_source_certificate.json)
lists every numerical modulus and its one residue. It is a finite actual
family, not a table of separately chosen best responses on different leaves.
The full numerical labels3n and9m cannot coincide because n and m are3-free.
No support or exponent label is merged. Every modulus is odd and greater
than one.

The q5 slot roles use leaves1,0,1 at exponents1,2,3 and leaf0 thereafter,
all in root0. The other six singleton supports have constant roles. For
the three fractional mixed supports, the head subsets and the deterministic
greedy tail of798 specify a single role for every n in increasing numerical
order. Constant-colour supports use that colour at every exponent vector.
The consumer reconstructs this finite prefix from798's neighboring
certificate, then independently reads the resulting original phases to
compute the raw caps below.

## 2. These pure-coordinate constants are attained

For j<k, the kth pure residue in(R2) is0 modq^j, while the jth is nonzero
modq^j. The three pure cylinders are therefore disjoint. Their actual
survivor measure and its normalized cylinder constant are

    z_q=1-q^(-1)-q^(-2)-q^(-3),
    C_q=1/z_q,   b_q=C_q/(q-1).                        (R4)

These C_q are the finite-family constants of this report, rather than the
larger limiting constants(q-1)/(q-2). In increasing prime order they are

    (125/94,343/286,1331/1198,2197/2014,
     4913/4606,6859/6478,12167/11614).

Every2 modq^e cylinder avoids all three pure exclusions: the first pure
class is1 modq, and the other two are0 modq. Consequently its normalized
pure-survivor mass is exactly C_q/q^e. The cap is attained for every
nonternary phase used in the listed mixed originals, before any star
deletion. Products give the exact pre-star cylinder mass C_D/n, where
C_D=product_(q in D)C_q. This does not say that the cylinders are disjoint
or that later star thinning preserves their full mass.

## 3. Reconstruct the raw root, leaf and no3 budgets

For every support D, define b_D=product_(q in D)b_q. A full numerical
original with nonternary modulus n has normalized cap

    a_n=(C_D/n)/b_D=product_(q in D)(q-1)/n.            (R5)

Let x_D,r be the sum of(R5) over the actual3n originals assigned to root r,
and y_D,l the corresponding sum over actual9n originals assigned to leaf l.
For |D|>=2 let z_D be the sum over the actual no3 originals n. Each quantity
is reconstructed from the listed phases, not supplied as a free parameter.

All three inventories use the same finite numerical cutoff. Thus

    sum_r x_D,r=sum_l y_D,l=z_D<1                     (|D|>=2),
    sum_r x_D,r=sum_l y_D,l<1                         (|D|=1). (R6)

The unspent budget is left unspent. In particular the mixed leaf coefficient
is

    c_D,l=z_D+x_D,group(l)+y_D,l,                       (R7)

not the completed expression1+x+y. The retained star mass is

    m_q,l=1-b_q[x_{q},group(l)+y_{q},l].               (R8)

Since raw inventory totals are at most one, m_q,l>=1-2b_q>0 and
0<=c_D,l<=3.

## 4. The same-source lower-bound proof also applies without padding

Let lambda_q be normalized Haar on the actual pure-q survivor. On leaf l
let A_q,l be the mass after the actual3q^j and9q^j star exclusions. The
union cap gives A_q,l>=m_q,l. Thin that actual star-survivor restriction by
the factor m_q,l/A_q,l. The resulting sigma_q,l has exact mass m_q,l, stays
on the actual survivor and is dominated by lambda_q.

The five-leaf source is the weighted product of these submeasures. The
actual union of mixed originals of support D has conditional probability
at most b_D c_D,l/product_(q in D)m_q,l. Disjoint supports depend on disjoint
coordinates. The support-intersection graph and one-clique Shearer argument
of Report789 therefore still apply. That argument only needs nonnegative
activities and c_D,l<=3; it never requires a lower bound c_D,l>=1.

Indeed the same clique complement, on7,11,13,17,19,23, has total activity
at most184697/233415<1, since the finite b_q in(R4) are no larger than the
old universal b_q. Hence its induced polynomials stay in the positive
region. This supplies the same valid signed full polynomial on each leaf,
including the case of a negative full polynomial. The retained physical
source is dominated by the one common probability law

    lambda=(fixed five-leaf law w) tensor product_q lambda_q.

No source is changed in response to a query.

Define

    a_U,l=b_U product_(q outside U)m_q,l.

The source's raw signed lower certificate on leaf l is exactly

    R_l=a_empty,l-sum_D a_D,l c_D,l
        +sum_disjoint{D,E} a_(D union E),l c_D,l c_E,l
        -sum_disjoint{D,E,F} a_(D union E union F),l c_D,l c_E,l c_F,l. (R9)

There are120 supports,546 disjoint pairs and210 disjoint triples; no four
mixed supports are disjoint. The consumer directly evaluates every term,
without replacing these raw arrays by an infinite completion or an error
bound around one. The five values are approximately

    (0.003080715834695239, 0.002908861849771719,
     0.0016810510603888372, 0.08155966331066414,
     0.0986393299052974).

All are strictly positive. Thus positive clipping makes no change here,
and F_raw=sum_l w_l max(R_l,0) has the value(R1). The [result](../../../frontier/cover-geometry/refined-capped-source/raw_finite_slot_source.json)
retains the exact rational arrays and values; displayed decimals are not
the acceptance criterion.

## 5. The complete-query hinge still needs more mass

For the same fixed w, the ternary comparator caps are r=2/3 and v=1/3.
The nonternary factors use the actual constants(R4):

    P(N_q>=j)=C_q q^(-(j-1)),   j>=2.

Their full means are1+b_q. The ternary full mean is1+r+3v/2. Thus the
complete product mean is evaluated by a finite product, retaining every
height tail. The finitely many product atoms below28 give

    H(t)=E N-t+sum_(j<t)(t-j)P(N=j).

For each integer t=0,...,27 the required source mass is H(t)/(28-t).
Every interval between consecutive integers has an affine H and hence
a monotone or constant ratio. Negative thresholds cannot improve0 because
0<E N<28; thresholds at least28 cannot certify an upper query cost below28.
The consumer compares all28 ratios. Their minimum occurs at t=16 and is T
in(R1).

Since F_raw<T, substituting this polynomial lower certificate into the
existing bound t+H(t)/mass cannot prove a value below28 for any threshold.
This says nothing about what using the larger true source mass could prove.
The one fixed full dominating law and its tight caps are kept throughout.

## 6. Removing whole contained classes restores the certificate

Sort the actual originals by increasing numerical modulus. Retain an
original a modm unless an already retained b modn satisfies

    n divides m,   a=b modn.                            (R10)

These conditions mean the ENTIRE m-class lies in that retained n-class.
The consumer retains one direct containing-original address for every
removed class. The kept classes are original classes; conversely every
removed class is contained in a kept one. Hence their two covered unions
are exactly equal, without any density approximation or phase change.

Exactly51 originals remain:3 and9, all21 pure classes(R2), the seven3q
originals, and the21 no3 originals2 modpq with p<q in Q. There are2899
literal containment witnesses. These witnesses and the complete retained
phase list are part of the result, not an assumption of the calculation.

The pure-coordinate survivor laws and the live ternary leaves are unchanged.
Rebuild the raw x/y/z from the51 actual classes, then apply the same source
construction and the same fixed weights. Directly aggregating the literal
pre-star cylinder masses C_D/n and expanding the120/546/210 support terms
gives

    F_kept=0.49097680418306305...>T.                    (R11)

The appropriate source thinning is performed again using the smaller star
inventory. This can change the constructed internal source; equality of
the covered union does not identify the old and new thinned submeasures.
Both are bounded by the same pure reference law lambda and avoid the same
full original union.

The same complete hinge coefficients now yield, at threshold4,

    complete normalized query cost
      <=4+H(4)/F_kept
      =8.100615846719924...<28.                        (R12)

The consumer compares all28 thresholds and verifies this bound. An independent
implementation uses an exponent-recursive label enumeration, reconstructs
literal phase incidences, and evaluates a set-packing recurrence instead of
the direct triple expansion. It obtains identical raw and retained responses,
all28 hinge values, the same51 originals and the containment witnesses.

Thus the initial failure was repaired by retaining a relation that a sum
of individual caps omitted: many original cylinders were already contained
in other original cylinders. This conclusion concerns this finite example.

## 7. An explicit survivor and the actual remaining distinction

The nonternary LCM has exponents(8,7,5,5,4,4,4) and equals

    L=58593296918333487151590568495066015625.

The integer

    x=2L=117186593836666974303181136990132031250

is4 mod9 and0 modL. It avoids0 mod3 and1 mod9; it avoids every nonzero pure
residue in(R2); and it avoids every remaining original, whose nonternary
residue is2. The consumer checks x against all2950 listed congruences.

The shared phase2 construction has considerable overlap and containment.
Numerical-slot realizability, finite actual phases, tight pure caps and
removal of unused-budget padding alone did not repair its unreduced cap
estimate; the explicit containment reduction did. No assertion of worst-case
geometry or an actual survivor mass upper bound is made.

Nor does this prove that irredundancy suffices in general. Existing
[Report546](../500-549/546-dense-irredundant-families-separate-stage-debits-from-actual-unions.md)
uses dense irredundant two-copy families to separate stage debits from true
unions, while [Report615](../600-649/615-nested-actual-incidences-force-unbounded-fixed-law-credit.md)
gives distinct-label irredundant families obstructing a specified fixed-law
incidence-credit certificate. Their hypotheses and methods differ from this
example, and neither is a claim that the present polynomial fails on every
irredundant family. They preclude treating this simple repair as a general
solution of the remaining source problem or Erdős#7.

## Verification

The [portable consumer](../../../frontier/cover-geometry/refined-capped-source/raw_finite_slot_source.py)
uses only the standard library and the neighboring798 allocation certificate.
It reconstructs the finite numerical prefix, checks every listed full
phase, computes raw x/y/z from those phases, expands(R9), evaluates the
complete hinge, verifies the explicit survivor, removes whole contained
classes with direct witnesses and recalculates the corrected response.
Normal and optimized Python runs agree, with49420 explicit checks.
Eight malformed controls are rejected with nonzero exit status: missing
and duplicated labels, changed mixed and pure phases, a forged raw budget,
a forged gap, a forged containing-original address and a forged corrected
response. The result is a finite certificate and repair for the stated
method, not a new noncoverage class or a Lean theorem.
