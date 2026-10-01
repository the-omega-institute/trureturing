# A175-cell actual head supplies a joint sixteen-response gluing criterion

The small5x7 boundary can be coupled to11,13,17,19 without treating the
head as independent of their active constraints. The sufficient
criterion below retains one actual head mask and one actual conditional
outside source, including all original outside heights. It gives a
finite jointly checkable mass/query gate for the later23/29 continuation.
It does not assert this gate is positive for every actual family.

Four explicit phase patterns on the same heads as the scalar obstruction
also admit arbitrary added core heights, including pure high powers,
by the same-source prefix-tail argument in
[Report717](717-four-fixed-shallow-families-survive-arbitrary-nonternary-heights.md).
Their initial shallow phases remain fixed hypotheses; this does not
close the universal arbitrary-phase quantifier.

The source and deletion-ratio mechanism reuses [Report663§7](../650-699/663-a-finite-field-library-covers-every-binary-leaf-layout.md) and [Report683§4](../650-699/683-paired-responses-tighten-complete-four-parent-owner-fees.md).
The new specialization is the four-coordinate signed response with
arbitrary pair, triple and full-support groups, its automatic induced
positivity after pair-cap clipping, and the explicit paid passage from
an actual first-digit head to all original5/7 heights. This is ordinary
mathematics and exact diagnostics, not new Lean verification.

## 1. One actual source and actual conditional data

Throughout, the complete finite original family has pairwise distinct
odd numerical moduli greater than one, supported on
{3,5,7,11,13,17,19,23,29}, and EVERY original satisfies v3(m)<=2.
This includes the later23/29-bearing originals. The five-leaf source
and its fixed root/leaf selectors are the declared ternary interface;
no higher ternary digits are discarded under this hypothesis.

Keep the five retained ternary leaves, root groups{0,1},{2,3,4}, weights
w=(1/4,1/4,1/6,1/6,1/6), and actual pure survivor laws lambda_q. Put
b_q=1/(q-2), C_q=(q-1)/(q-2). Write

    u=(l,r5,r7), rho_q(r)=lambda_q(x_q=r modq).

Let U(u) be the actual compatibility mask of the seven possible
first-level originals15,45,21,63,35,105,315. Their original residues
and root/leaf owners all come from the SAME family. Choose0<=f<=U,
withf=0 on null pure-source head atoms. The initial head submeasure has
mass at u equal to

    a(u)=w_l rho5(r5)rho7(r7) f(u).

Now take B={11,13,17,19}. Split every remaining original in the core
3,5,7,B according to whether its5 and7 exponents are each at most1.
At fixedu all such SHALLOW-HEAD original predicates depend only on the
outside coordinates, with their globally fixed original phases.

For eachq inB delete every shallow-head original whose outside support
is exactly{q}. This is one actual union of q-adic cylinders; pure q
originals are already absent in lambda_q. Let

    xi_(q,u)=lambda_q restricted to this actual unary avoidance,
    m_q(u)=xi_(q,u)(1).

For everyD subsetB with|D|>=2, let A_D(u) be the union of actual
shallow-head originals with outside supportD, as an event on those
coordinates. Choose a valid UNNORMALIZED cap

    [product_(q inD)xi_(q,u)](A_D(u)) <= kappa_D(u)
                         <= product_(q inD)m_q(u).    (JG1)

An available raw union upper can always be clipped at the product
mass to satisfyJG1. Actual q-adic union computations or sharper
same-source caps are also allowed. All full original numerical labels
and outside exponent vectors remain in this data. The cap values are
not selected independently to impersonate a realizable phase layout.

## 2. Four-coordinate source and sixteen simultaneous responses

ForV subsetB define

    Z_V(u)=product_(q inV)m_q(u)
       -sum_(D subsetV, |D|>=2)kappa_D(u)
                               product_(q inV minusD)m_q(u)
       +1_(V=B)sum_(three complementary pair supportsD,Dc)
                               kappa_D(u)kappa_Dc(u). (JG2)

This is the unnormalized signed sum over disjoint supports. In four
coordinates only the displayed three independent pairs can occur.
LetZ=Z_B. The direct probability proof bundles the six pair events into
three complementary-support unions, computes each bundle using
coordinate independence, and applies a union bound to these bundles
and all triple/full-support events. It gives actual outside avoidance
mass at leastZ. JG1 makes substitution of upper caps monotone.

More is true on any row withZ>0. Such a row has everym_q>0, becauseJG1
and the direct bound implyZ<=product m. Normalizec_D=kappa_D/product_Dm.
All pair capsc_D are at most1. The full normalized polynomial

    q=1-sum_D c_D+sum_(three complementary pairs)c_D c_Dc

has derivative-1+c_Dc<=0 at a pair coordinate, and derivative-1 at a
triple or full-support coordinate. This remains true throughout the
entire downward cap box. Every event-induced subgraph polynomial is
obtained by setting omitted support caps to0, so every one is at least
the positive fullq. This is a verified special property of the present
four-coordinate shape, not an assumption that full-polynomial positivity
suffices on arbitrary dependency graphs.

The usual event-deletion ratio argument now applies. For completeness,
ifP_A is actual avoidance of a finite set of event groups andq_A its
positive induced polynomial, joint independence of one event from its
nonneighbors gives

    P_A >= P_(A minusv)-c_v P_(A minus N[v]).

Inductively telescope previously proved ratios on smaller event sets
and divide byP_(A minusv)>0 to obtain

    P_A/P_(A minusv) >= q_A/q_(A minusv).

Telescoping yieldsP_all/P_out>=q_all/q_out for any deleted group set.
This is the same mechanism used by the existing conditional response
construction. All divisions occur only on the positive row.

Letgamma_u be the ACTUAL product ofxi_(q,u), restricted to avoidance
of every remaining shallow-head outside support group. Uniformly thin
it to massZ:

    zeta_u=[Z/gamma_u(1)]gamma_u       ifZ>0;
    zeta_u=0                         ifZ<=0.          (JG3)

No zero-mass row is divided by. For every queried outside supportT,
the SAME kernelzeta_u simultaneously satisfies

    (zeta_u)_T <= H_T(u) product_(q inT)xi_(q,u)
               <= H_T(u) product_(q inT)lambda_q,
    H_T(u)=1_(Z>0) Z_(B minusT)(u).                  (JG4)

To see this, avoidance of groups disjoint fromT is independent of a
T-query under the normalized unary product. Its avoidance ratio to the
full event set is bounded by the polynomial ratio just proved. Multiply
by the one thinning factor inJG3 and restore all unary masses. This
is a marginal-MEASURE inequality for every nonnegative payoff, not only
an isolated cylinder estimate. In particularH_empty=[Z]+ andH_B is
1 on retained rows. AllH_T on a retained row are strictly positive.

## 3. Pay all head-deep originals on that same source

Integratezeta_u against the constructed head source. Its mass is

    S(f)=sum_u a(u)[Z(u)]+.                          (JG5)

This is one actual core submeasure dominated by the original pure
product with ternary weightsw. Delete every remaining original having
5-exponent>=2 or7-exponent>=2. Originals with empty outside support
have the complete bound

    tau_head=(1/2+1/4)(b5/5+b7/7)
             +(7/4)[b5 b7-(C5/5)(C7/7)]
            =1/14+11/300=227/2100.

The first term pays the remaining one-axis stars3q^e and9q^e at
heights e>=2; pure powers are already excluded. The second pays the
mixed5/7 labels except exponent pair(1,1), at all three ternary
heights. These are disjoint original-label inventories.

For originals with nonempty outside support inB, the complete nonternary
head coefficient is

    (1+b5)(1+b7)-(1+C5/5)(1+C7/7)=61/525.

The no3/3/9 inventories have total weighted cap at most1+1/2+1/4=7/4.
Thus every outside exponent vector and support, including arbitrarily
large finite heights, is paid by

    tau_cross=(61/300)[product_(q inB)(1+b_q)-1]
             =(61/300)(69/187)=1403/18700.

The resulting SAME actual final core source nu therefore has mass

    alpha>=S(f)-tau,
    tau=17978/98175.                                 (JG6)

This is a common upper loss bound. One may replace it by a rigorously
smaller actual tail bound on this same source. There is no assertion
that all complete tail bounds are attained together, and no high
original exponent was truncated or silently discarded.

## 4. Four hundred thirty-two finite query modes, including the unit

For each head axisq=5,7 use the finite modes

    whole: rho_q;
    first(r): rho_q(r)delta_r, fee1;
    deep(r): delta_r, fee b_q/q.

The whole mode has fee1. The deep fee sums everyheight>=2 using the
actual base cylinder cap. For ternary height0,1,2 use respectively the
whole, root and leaf selector menus, each with fee1. For any nonnegative
head functiong defineS_mode(g) by summingw_l g(u) against the selected
head row vectors and one ternary selector, THEN maximizing over one
global selector/residue tuple. Null pure-source head atoms are omitted.
There is no independent phase choice at different leaves of a screen.

For each outside query supportT, sum every positive exponent at its
coordinates, giving feeb_T=product_(q inT)b_q. JG4 makes the associated
head kernel exactlyf(u)H_T(u). Define

    K(f)=sum_(head modes,T except unit)
           [head mode fees] b_T S_mode(f H_T).       (JG7)

There are27 head mode types and16 outside supports, hence432 types
including the unit and431 nonunit types. The unit is the whole-head,
T=empty readingS(f); it is excluded inJG7. Every full original numerical
query label is bounded at its own complete exponent vector. Summing
those nonnegative upper bounds givesJG7 with the full geometric tails.
It does not claim all independently maximal queries are simultaneously
attained by an actual original family.

The source restriction inJG6 decreases every nonnegative nonunit
query. WhenS(f)>tau, its normalized law therefore has

    R(nu/alpha)<=K(f)/(S(f)-tau).                     (JG8)

Consequently

    (566/49)[S(f)-tau] > K(f)                        (JG9)

is a jointly checkable sufficient condition for the existing actual
pure-conditioned23/29 continuation. Every source, response, tail and
query inJG9 refers to the same actual original family and the same
chosenf. It is not a combination of separate optimal source laws.

For fixed actual head and conditional data, JG9 is a finite rational
feasibility problem:0<=f<=U, one actual175-cell kernel, sixteen fixed
conditional responses, and epigraph inequalities for all literal global
selector tuples inJG7. It has not been proved that every actual family
admits suchf, nor that this uniform tail estimate is always sufficient.
That is the substantive remaining quantifier, not a consequence of
writing a finite interface or establishing its correctness.

## 5. Verification and reuse boundary

The paired checker verifies the three-bundle union inequality on all
2048 event-indicator patterns. Two independent finite product-law
fixtures use actual overlapping events, their actual or inflated valid
caps, actual full avoidance, and one common thinning. It checks all81
marginal atoms over the16 outside supports for each fixture, plus zero
unary and saturated-pair boundary rows. The complete tail constants
are verified exactly. These fixtures are probability models, not
asserted odd-covering families or evidence for a uniform positive gate.

Reports663 and683 already supply the conditional-source/deletion-ratio
method. [Report689](../650-699/689-actual-pure-support-averaging-gives-a-finite-all-height-query-interface.md) explains why arbitrary deep sources cannot simply be
averaged under caps-only hypotheses; the present construction instead
chooses a prefix-constant head kernel and explicitly pays all omitted
head-deep originals. The four-coordinate derivative argument is the
required new condition check for applying the older ratio mechanism to
this support shape. The checker and prose do not claim new Lean proof,
a new general Shearer theorem, or a solved unrestricted Erdős#7.

The [standalone exact diagnostic](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_gluing.py)
and its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_gluing.json)
replay without external packages. An independent enumeration of disjoint
support families checks the same responses, plus a third actual finite
probability pattern with different endpoint choices: 243 marginal atoms
in total. These checks support the finite calculations; the preceding
argument supplies the general inequalities.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_gluing.py
```
