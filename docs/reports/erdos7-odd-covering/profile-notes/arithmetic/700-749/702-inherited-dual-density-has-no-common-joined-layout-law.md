# The inherited dual density has no common joined-layout law

The specific pointwise domination route proposed in
[Report701](701-equal-joined-boundaries-can-have-different-remaining-costs.md)
is impossible on the actual109 source. There is no probability distribution
on complete33-label layouts whose expected selected charge dominates the
inherited density R everywhere on that source. All eight central phases and
all exterior phases are free in this statement; retaining the old central
layout law is not assumed.

An explicit probability measure tau, supported on actual surviving cylinders,
separates R from EVERY full-layout mixture:

    integral R d tau=4934901206239460693/288915000000000000,
    K33(tau)=239468/14025,
    integral R d tau-K33(tau)
       =1860406239460693/288915000000000000
       =0.006439285739614395...>0.                         (JD1)

This closes a particular dual-lift question. It does not exclude every dual
certificate for the33-label gate, rule out its target193/100000, or give a
positive retained field for that gate. All remaining original-loss and
all-height screen fees still matter. Unrestricted Erdős#7 remains unresolved.
The result uses ordinary mathematics and exact rational checks, not new Lean
verification.
[Report704](704-a-full-joined-dual-excludes-the-retention-target.md) separately excludes the full gate target by changing both query-row and layout probabilities; it does not use the impossible pointwise domination here.

## The density whose transfer fails

Keep the109 original numerical moduli and fixed phases, the actual source
sigma and complete-screen normalizations. Let

    D0={3,5,9,15,25,45,75,225},  Q={7,11,13,17,19}.

For a complete33-label layout a, let L_a be exactly699's selected charge:
the central block n_a^2+2n_a, the five exterior prime unaries of weight3,
and one triangle for each of the20 remaining prime pairs. A triangle's
charge is

    2 I_p I_q+3 I_pq+2 I_p I_pq+2 I_q I_pq.

The same numerical label has the same phase wherever it occurs. The maximum
K33(tau)=max_a integral L_a d tau allows independent choices for all33 labels.

The proposed transfer keeps698's old-screen row fractions. Its desired
density, in units of c=1084133/201247200, is

    R=h8+sum_(25 exterior selected groups j) v_j E_698[row_j],

where h8 is the charge of698's rational mixture of225 complete centered
eight-label layouts. Each of the25 exterior groups has total row fraction
one, and its292 rows are shallow. These data are fixed by the pinned698
witness. A pooled free-root token is interpreted as its uniform literal-root
average, consistently in both R and the test measure.

No choice of a new full-layout probability law pi can satisfy

    H_pi=E_pi L_a >= R  sigma-almost everywhere.           (JD2)

This includes arbitrary correlations among its33 phases. Independent
per-group maximizers are not substituted for a common law.

## A small measure on the actual survivor source

For each x in Z/225Z define the integer weight

    w(x)=8   if x mod45 is one of3,12,33,42;
          12 if x mod45=25;
          9  if x mod45=43;
          11 if x mod45=7 and x!=52;
          0  otherwise.

There are34 positive central values, and sum_x w(x)=309. Give the central
coarse value x probability w(x)/309. Inside that coarse leaf use the original
pure-survivor conditional law. Independently at each q in Q, choose the
first root uniformly from{2,...,q-1}, and keep its actual conditional law in
the unexposed digits. This defines ONE probability measure tau.

Every resulting cylinder lies in the actual109 survivor support. The source
check resolves the original central pure classes at729 and15625, retains
only their real survivors, and checks incompatibility with every remaining
original using the same prime coordinates. This qualification matters:
coarse leaves such as2 mod25 contain deleted higher-pure descendants, so the
construction does not replace the pure-survivor law by an intact Haar leaf.
Each selected actual cylinder has positive sigma-mass. Direct comparison of
the34 cell masses gives

    t=19261/103680,  t tau<=sigma.

Thus tau is absolutely continuous with respect to sigma with bounded density,
and this explicit positive scalar multiple is an admissible retained measure.

The separating argument only needs this support and absolute-continuity
fact. It does not treat tau itself as a retention bounded by one or count
a new survivor created by the choice of measure.

## Exact optimization of every complete layout on tau

The product form gives a shorter exact calculation of K33 than a general
field search. Put

    m_p(r)=sum_(x modp=r)w(x)/309,  p=3,5,
    L=sum_(q in Q)1/(q-2)=4439/8415,
    B=9 sum_(q<r in Q)1/[(q-2)(r-2)]=13238/14025.

Let C(a,b) be the exact conditional maximum of the central-eight block when
its3-query phase is a and its5-query phase is b. The other six central labels
remain independent. For each fixed(a,b), enumerate all37,800 choices of the
five free phases for9,15,25,45,75 that hit the34-point support. Off-support
choices may be discarded: replacing a zero indicator by any supported one
cannot decrease this nonnegative increasing charge. Finally the225 label
hits at most one central point, so maximize its incremental charge
w(x)(2n(x)+3) over those points. This gives the complete numerator table
with common denominator309:

| a \\ b | 0 | 1 | 2 | 3 | 4 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0 | 2655 | 2193 | 3147 | 3140 | 2193 |
| 1 | 3352 | 2620 | 3195 | 3175 | 2620 |
| 2 | 2175 | 1563 | 2120 | 2063 | 1563 |

For fixed central phase a_p, the best p,q triangle equals

    [2m_p(a_p)+max_u(5+2*1_{u=a_p})m_p(u)]/(q-2).

To see this, an exterior prime phase can be chosen in its supported roots;
its mass is1/(q-2). The independent pq query may choose any central root u,
and choosing its exterior root equal to the exterior prime phase maximizes
the positive composite terms. A phase outside the supported exterior roots
cannot improve any term. All20 triangle maxima are attained together by
using root2 for every exterior prime, the optimizing central root for each
central-exterior composite, and(2,2) for every exterior-only composite.
Thus, writing

    A_p(a)=2m_p(a)+max_u(5+2*1_{u=a})m_p(u),

we obtain the exact full-layout formula

    K33(tau)=max_(a,b)[C(a,b)+3L+B+L(A_3(a)+A_5(b))].       (JD3)

There is no common-center assumption and no independent optimization of
incompatible margins in(JD3). Conditional on the shared3 and5 choices, all
remaining exterior choices have the simultaneous completion just described.
The central choices are optimized by the exhaustive five-phase calculation
and the exact final225 maximization.

The maximum is239468/14025. An attaining central layout is

    (a3,a5,a9,a15,a25,a45,a75,a225)=(0,2,3,12,7,12,57,57).

Together with outside prime phase2, central-exterior composite roots(0,2)
or(2,2), and all exterior composite roots(2,2), this is one literal complete
layout. Its central phases are not all reductions of a common center.

## Separation and the remaining research obligation

Direct rational evaluation of698's same225 central rows and292 exterior
rows gives the first value in(JD1). For any probability law pi on layouts,

    integral H_pi d tau
       =E_pi[integral L_a d tau]<=K33(tau)<integral R d tau.

Because tau is absolutely continuous with respect to the actual source,
this contradicts(JD2). The argument excludes equality as well as domination.
It is stronger than a mismatch of separately prescribed row marginals and
stronger than an obstruction restricted to a fixed central layout law.

A further certificate may change the old-screen row fractions, or permit
H_pi<R on some source states and evaluate the resulting deficit in the SAME
full residual integral

    integral [g-d33]_+ d sigma.

The present separation does not lower-bound that residual integral: a debit
deficit and the positive-part residual are different quantities. Nor can a
value from a different retained field or source be used to pay it. Therefore
the conclusion does not transfer698's gate obstruction to699, invalidate698
for its own criterion, or settle whether699 admits a paying field.

## The separating retention does not pay the full gate

For the explicit admissible retention f sigma=t tau above, keeping ALL512
screens and all original losses gives

    K33(t tau)=6166301/1944000,
    G33(t tau)=-2364541350521439962962651
                /22219458019105374720000000
              =-0.10641759796698425... .                  (JD4)

The change from the old independent-screen gate is genuinely positive,
763033403927/312979645440000, but the complete result is negative. Thus the
same explicit field separates the proposed dual density and fails the primal
target; these are distinct conclusions.

The all-height screen calculation has a product form. For outside support T,
the maximal normalized factor is product_(q in T)(q-1)/(q-2). The first-root
query attains it; every deeper query in a full supported root has factor1.
For the central modes, evaluate the same actual pure-survivor selectors on
the finite weighted central law. Modes0,1,2 give respectively the whole
coordinate, root indicator and second-level indicator. Mode3 has multiplier
9/2 on a strong ternary leaf and729/82 on its weak leaf4 mod9; the quinary
values are15 and9375/469 on the weak leaf2 mod25. These are the unchanged
complete-screen reductions of689/690, not a truncation at the largest
displayed exponent. Maximizing each of the16 central modes and multiplying
by the outside factor gives every one of the512 screens in(JD4).

An independent calculation supplies the explicit category field with
denominator36 to the existing retained-field engine. All512 screens and512
original coefficients agree exactly with the product calculation. The
engine passes10,722 checks over all2,125,830 positive source categories;
the general joined separator passes3,205 checks and returns the same(JD4).
The verifier below includes the complete gate value and all512 screen values.

## Verification and reproduction

The witness fixes the34 small integer weights and outside root sets; the
verifier pins the original source and698 row data and derives the exact
values. Candidate optimization is absent from the verifier. The
standard-library verifier reconstructs the actual pure survivors,
verifies all109 originals, evaluates the existing698 fractions and computes
the full15-condition maximum(JD3). It independently checks an attaining full
layout from its121 literal atoms. The final run passes12,682 checks, including
the complete567,000 central baselines and the complete gate computation; it imports neither an optimizer nor
the existing separator.

A separate run constructs all21 pair tables and the central fine marginal
from that same product measure and uses699's general joined separator. It
returns the same value with3,104 checks. The independent joined auditor
reconstructs all121 literal factors and exhausts all4,849,845 original root
tuples without dominance pruning; it agrees with(JD3). The separate
567,000-baseline enumeration checks the15 central upper bounds themselves;
checking attaining layouts alone would not establish those upper bounds.

From the repository root, the standalone proof check and optional common
measure export are:

```sh
research_data=docs/reports/erdos7-odd-covering/frontier/cover-geometry
python3 -I -S -B -O "$research_data/joined33_dual_lift_obstruction.py" --output /tmp/joined33_dual_lift.json --joined-input /tmp/joined33_dual_lift_input.json
```

With NumPy installed, the two existing general checks can then be reused:

```sh
python3 -I -B -O "$research_data/joined33_separator.py" --input /tmp/joined33_dual_lift_input.json --output /tmp/joined33_dual_lift_general.json
python3 -I -B -O "$research_data/joined33_independent_audit.py" --pair /tmp/joined33_dual_lift_input.json /tmp/joined33_dual_lift_general.json --output /tmp/joined33_dual_lift_independent.json
```
