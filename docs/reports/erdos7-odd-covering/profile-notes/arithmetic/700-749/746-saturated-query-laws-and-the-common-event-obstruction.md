# Full saturated-query convex profiles still need the actual mixed-event incidence

This result uses only the first, hardest canonical pruned45 shape. It is an
ordinary proof with exact finite checks, not Lean. It locates the
information lost by replacing a fixed mixed-deletion event with an
arbitrary event of a prescribed mass.

## 1. Seven genuine zero-inclusive partial-query comparison laws

For nonempty S subset{3,5,7}, a saturated partial query uses precisely the
old315 divisor slots whose exponents equal the old cap at every p in S:
cap2 at3, cap1 at5 and7. Its phases remain arbitrary per numerical label.
The function can be0; it has no artificial unit lower bound.

On the SAME actual pruned315 source, the independent D2 construction yields
F_S<=icx Y_S with the following integer stop-loss caps H_S(t):

|S|maximal load K|H_S(0),...,H_S(K-1)|
|---|---:|---|
|3|4|35/83, 11/78, 2/77, 1/77|
|5|6|7/9, 11/27, 1/6, 5/77, 2/77, 1/77|
|7|6|6/11, 25/77, 1/7, 5/77, 2/77, 1/77|
|3,5|2|1/11, 1/77|
|3,7|2|5/77, 1/77|
|5,7|3|9/77, 4/77, 1/77|
|3,5,7|1|1/77|

For S not containing7, split F_S=A+B_z. The45 query slots are{9,45},
{5,15,45}, or{45}. For h(v)=(v-t)_+, the complete sufficient D2 check is

    5 sum_x h(A(x)) + max_B sum_j h(A^up_j+B^up_j)
      +sum_(d=3,5,9,15,45) max_(d-cylinder C)
                   sum_(x in S45 intersect C)(g-h(A(x)))_+
      <=6*17*g.

The checker enumerates every effective partial A, every histogram B, and
every old deletion cylinder. Quantile costs use histogram count transport.
A rational piecewise-affine iteration proposes g; the final displayed
inequality is then verified directly for every layout, independently of
whether the iteration found an optimum. When7 belongs to S, A=0, and the
sufficient bound is max_B sum h(B)/77. Its B slots include the unit only
for S={7}, since the actual F is then a positive-seven block.

Set H_S(K)=H_S(K+1)=0 and H_S(-1)=1+H_S(0). The probabilities

    P(Y_S=y)=H_S(y-1)-2H_S(y)+H_S(y+1), y=0,...,K

are all nonnegative, sum to1, and recover the entire displayed profile.
Therefore these are actual auxiliary probability laws, not signed
functionals. The mean caps exactly reproduce the earlier partial D2 means.
Every assertion is uniform over all queries on the ONE actual source;
no claim is made that different query extremizers are simultaneously actual.

## 2. Genuine outside transport followed by one actual restriction

Let J be empty,{23}, or{19,23}, with the five outside primes11,...,23 otherwise
shallow. The pure-survivor product comparison supplies the same multiplier M_J
as the already checked actual-source construction. For every saturated FULL
old query, now including all permitted outside cofactors and heights,

    F_S under sigma_J <=icx Z_S=Y_S M_J.

The proof uses the event-increment lemma and Jensen separately for each
fixed auxiliary height. Since these partial queries can vanish, absent
auxiliary layers may be padded with0. No unit assumption is introduced.
The products are genuine probability comparisons and all expectations here
are finite.

Condition the SAME sigma_J on the SAME actual old mixed-avoidance event E_J,
whose mass is at least the already certified delta_J. For every S,

    E_(sigma_J|E_J) F_S <= beta'_S
       =inf_(a>=0) [a+E(Z_S-a)_+/delta_J].

This is the mean of the upper delta_J tail. Each scalar cutoff may be
optimized separately: it is only a proof parameter for a uniform bound,
not a choice of a different source or different retained event. The seven
bounds may therefore be summed as upper bounds, but their sum is not
asserted to be the actual joint optimum.

Exact geometric-tail evaluation gives:

|Unrestricted outside axes|best conditional bound for F3,F5,F7|sum_S beta'_S prod_(p in S)1/(p-1)|
|---|---|---:|
|none|3.507560005, 5.912485097, 5.489934924|4.468928081382323|
|23|3.640303793, 6.086532558, 5.703553503|4.640533715378184|
|19,23|3.883068252, 6.404785444, 6.016026226|4.941028693226552|

The first case's optimal cutoffs for the seven fields in table order are
(2,4,3,0,0,0,0); the next two are(2,4,3,0,0,0,0) and(2,4,4,1,0,0,0).
Thus the failure is not caused by retaining cutoff8 or using only means.
Every bound is an exact fraction in the result JSON. Infinite auxiliary
expectations are handled by closed geometric-tail formulas. The finite
low region determines each quantile exactly; no tail is discarded.

## 3. A single finite joint relaxation also fails

The preceding sum could overestimate jointly attainable values. To address
that concern explicitly, construct all seven Y_S from ONE uniform quantile
variable U. Their joint law has13 rational atoms. Independently draw the
SAME shallow outside multiplier M=2^(B11+...+B23), which has6 values. Define

    F_S=Y_S(U) M,
    W=sum_S F_S prod_(p in S)1/(p-1).

This is one finite78-atom raw source with exactly the required seven marginal
comparison laws and one shared auxiliary outside multiplier. Retain the top

    delta=1243487/13077504

mass of W, splitting a threshold atom if necessary. The threshold is5/2.
A split can be represented by two copies of the same state, one retained
and one discarded, so this is literally one event in one finite probability
model. On that event,

    E W=491126096519693/111577640854680
       =4.401653348804365... >1.

The explicit joint source and retained atoms are included in the witness
JSON. The code verifies its mass, every marginal, its single-event quantile,
and all seven conditional means. No independent extremizers were declared
simultaneously attainable; the common realization is supplied explicitly.

The existing full-query comparison and ancestor-projection checks can also
be retained in this relaxation. For D_S=product_(p in S)(H_p+1), exact checks
give

    max(1,D_S Y_S)<=icx Y_full

at every integer head threshold. Consequently the same model can include
G_S=max(1,D_S F_S), with G_S>=D_S F_S and G_S<=icx Y_full M. This follows from
G_S<=M max(1,D_S Y_S) and independent positive multiplication. Thus the
obstruction persists after adding the full-query convex bounds and these
ancestor-completion inequalities.

THIS IS A RELAXATION, NOT AN ACTUAL CRT CONSTRUCTION. The head comparison
laws mix sufficient bounds from different actual-source arrangements. For
example the marginal probability P(Y_3=0)=4657/6474 cannot be a probability
on a uniform pruned315 source with77<=N<=102. The witness establishes that
passing only these marginal profiles, projection inequalities, the product
multiplier and an unqualified retained mass loses necessary information.
It does not refute the actual covering conjecture or all source choices.

## 4. The exact retention-only repair threshold

All seven Y_S have nonzero probability at most10/27. The multiplier M_J is
strictly positive, so this remains true for Z_S. Let

    R_J=sum_S E Z_S prod_(p in S)1/(p-1).

The exact values are

|J|R_J|
|---|---:|
|empty|46049941717/63611412480 =0.7239257850386284...|
|23|22023885169/30359992320 =0.7254245961877767...|
|19,23|68185403/93703680 =0.7276704927704013...|

Each R_J lies strictly between10/27 and1. If a proposed retained mass delta
is at least10/27, every upper-tail mean has cutoff0 and the total upper bound
is exactly R_J/delta. Upper-tail means are nonincreasing with delta. Therefore,
for THESE fixed marginal comparisons and no further event information,

    sum_S beta'_S(delta) prod_(p in S)1/(p-1)<1
        iff delta>R_J.

This identifies the precise sufficient mass threshold of this route, not
just a failed value. The common-quantile relaxation has the same zero-mass
threshold and supplies a matching failure when the mass is too small.

## 5. The needed information concerns the actual deletion event

The calculations above show that the current marginal comparisons,
ancestor inequalities and a scalar retained mass allow a joint relaxation
whose marked deletion debit exceeds1. They do not rule out stronger
marginal estimates derived from actual source geometry.

The required quantities are joint integrals such as

    integral 1_(Eoutside) F_(S,query) d sigma,

normalized by the SAME actual mass sigma(Eoutside). Their numerator and
denominator must use the original outside phases and the same old-row
source. The [actual marked-cylinder example](747-an-actual-marked-boundary-restores-a-core-height-continuation.md)
constructs one original family for which the retention-only threshold
fails, while its full marked-cylinder data certify a positive all-height
core continuation. It keeps all outside cofactors in its queries.

## Exact consumer

The [consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_saturated_partial_obstruction.py)
and [result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_saturated_partial_obstruction.json)
recompute every partial D2 inequality and positive comparison law, the
three complete geometric-tail budgets and the78-atom joint relaxation.
The full raw and retained joint atoms are included, allowing the common
mass, each marginal and the weighted score to be checked directly.

The consumer pins the inherited head and core-interface results, verifies
the seven means agree with that interface, and rejects stale output.
It does not assert the relaxation is generated by actual congruence
classes. The separate variables completing different saturated faces
are separate allowed full queries; no common full-query maximizer is
assumed. Infinite auxiliary tails are evaluated analytically, while
actual original inventories remain finite.

The current partial interface alone does not settle unrestricted Erdős#7.
No new Lean verification or covering counterexample is claimed.

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_saturated_partial_obstruction.py
```
