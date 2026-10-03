# Numerical-slot boundaries retain complete cap tails with explicit error

The two completed-simplex clipping witnesses A and B do not belong to the
smaller cap-completion domain obtained by retaining the indivisible weight
of every original numerical label. A fails at the first5-power slot; B
passes the first two slots and fails at the third. Positive exact distances
exclude approximation by label-preserving completions, including all
within-root relabelings of the witnesses.

This supplies a safe smaller domain for the existing depth-two source
construction, together with finite branch cells and a complete infinite-tail
error. It does not supply a positive uniform clipped lower bound or settle
unrestricted Erdős#7. All statements here are ordinary mathematics and exact
rational checks, not new Lean verification.

The cap polynomial has exactly the seven nonternary axes listed below and
retains the old hypothesis that the source originals have ternary depth at
most2. Only their nonternary heights are unrestricted. This is not a source
theorem for arbitrary original3-power heights or arbitrary support size.

## 1. Three quantities that must remain distinct

Keep one actual finite family, its distinct numerical labels, and the one
globally fixed phase of each present label. Use Report789's five live
ternary leaves, root groups{0,1} and{2,3,4}, and

    Q=(5,7,11,13,17,19,23),  C_q=(q-1)/(q-2),  b_q=1/(q-2).

The actual pure-q originals determine the same normalized pure-survivor
law lambda_q. Its cylinder cap is C_q/q^j. The q^j,3q^j and9q^j labels
remain different labels with their own fixed phases; none is replaced by a
phase chosen independently on each leaf.

For the3q^j inventory, assign its cap to its actual live root if the label
is present and meets that root. Otherwise assign zero. For the9q^j
inventory do the same with its actual live leaf. Dividing each complete
inventory cap b_q out gives one indivisible weight per exponent,

    a_qj=(C_q/q^j)/b_q=(q-1)/q^j,   sum_(j>=1)a_qj=1.       (N1)

Thus an actual raw normalized cap vector is a sum of a_qj times one colour
vector, or zero for an inactive slot. This is an upper-cap allocation, not
the true additional deletion mass: actual cylinders may overlap or lose
mass against earlier exclusions.

Report789 permits arbitrary padding of this raw vector to a probability
simplex. That larger domain is a valid relaxation. A point excluded below
can still be an arbitrary padding of a small raw vector, including zero.
Consequently “this full vector is not an actual allocation” would not by
itself repair the old relaxed-domain obstruction.

The necessary stronger assertion is existential: every actual family has
at least one dominating completion in the smaller domain now constructed.

## 2. Complete numerical slots, rather than splitting their caps

For every exponent j, keep the actual root or leaf colour whenever active.
If inactive, choose a designated colour, for example colour0. Sum every
slot, including the complete infinite tail. This defines a full vector

    v=sum_(j>=1)a_qj e_(t_j),                              (N2)

which dominates the actual raw vector coordinatewise. The choices for
3q^j and9q^j are separate. A colour assigned to an inactive slot is only
upper-budget padding; no original congruence or phase is added.

For k colours let D(q,k) denote all vectors(N2). Its first J slots give
the finite containing domain

    F_J(q,k)=union_(t_1,...,t_J)
      [sum_(j=1..J)a_qj e_(t_j)+q^(-J) Delta_(k-1)].       (N3)

The tail coefficient is its full infinite mass, not a truncation error
silently set to zero. These domains are nested. Their intersection is
D(q,k): a consistent infinite choice of finite words exists by the finite
branching tree argument, and the tail tends uniformly to zero. Equivalently,
D(q,k) is the compact image of the compact colour-sequence space under
the uniformly convergent series(N2).

Every point of F_J lies within l1-distance2q^(-J) of D(q,k), by choosing
any one tail colour. At the first layer,

    D(q,k) subset union_t {v in Delta: v_t>=(q-1)/q}.      (N4)

After subtracting a chosen first slot, exactly the same test applies to
the rescaled tail. For q>=3 at most one coordinate can accommodate the
next slot: two would exceed the entire remaining mass. Thus membership
in F_J is checked by a unique greedy digit extraction or a definite
failure, without a numerical optimization.

Missing the first actual label bounds its actual raw total by1/q. It
does not block this completion: the missing first slot can be assigned a
padding colour and(N4) follows. We assert the existence of this completion,
not that every arbitrary padding obeys(N4).

## 3. The existing actual-source argument survives this restriction

Let u_q and v_q be the completed root and leaf vectors just constructed,
and let

    m_ql=1-b_q(u_q,group(l)+v_ql).

Their coordinatewise domination bounds the actual star deletion union,
so its survivor mass A_ql satisfies A_ql>=m_ql>=1-2b_q>0. Use exactly
Report789's physical submeasure

    sigma_ql=(m_ql/A_ql) lambda_q restricted to actual star survival.

It has exact mass m_ql and remains dominated by lambda_q. Hence the same
signed Shearer bound applies at this selected completed point, and the
same full probability-weighted product law dominates the actual source.
No monotonicity of a signed polynomial under arbitrary budget padding is
needed. The moments and query caps retain that common dominating law.

For a mixed nonternary support D, let d=product_(q in D)q^(j_q), j_q>=1.
The three labels d,3d,9d have separate inventories and fixed phases. Their
per-label product cap is C_D/d, with C_D=product_(q in D)C_q. Relative
to b_D=product_(q in D)b_q, the indivisible slot weight is

    a_(D,j)=(C_D/d)/b_D=product_(q in D)(q-1)/q^(j_q).    (N5)

The3d and9d allocations receive the same slotwise completion argument.
Their leading numerical slot d=product_(q in D)q has weight
lambda_D=product_(q in D)(1-1/q). Root and leaf marginals must each have
a component at least lambda_D in any such completion. One can also pair
the two slot colours into a ten-colour root/leaf role. Only the marginals
enter the source response, so rejection of an arbitrary ten-colour
representation alone would not suffice when another pairing has the same
marginals. The tests below reject the marginals themselves.

For any finite retained exponent set E, the analogue of(N3) has prefix
sum over E and the entire remaining mass1-sum_E a_(D,j). A rectangular
set1<=j_q<=J_q has remaining mass

    epsilon_D=1-product_(q in D)(1-q^(-J_q)).              (N6)

This is an upper-domain construction, not a claim that all cap equalities
or completed phases can simultaneously be attained by physical originals.

## 4. Exact exclusion of A, B and their relabelings

Witness A has q5 leaf vector

    (0,0,2226446,2771867,1818236)/6816549.

Every entry is below4/5. It lies outside F_1(5,5). Its exact l1-distance
to that whole union of five translated simplices is

    26813722/34082745 > 0.                               (N7)

Independently, A's mixed support{5,7,11} has root vector
(104825,67174)/171999. Its larger entry is below the leading slot
weight48/77, so this mixed root allocation also fails its first layer.

Witness B has q5 leaf vector

    (394292,1877891,0,0,0)/2272183.

The4/5 slot must go to leaf1. The next4/25 slot must go to leaf0.
The remaining vector is

    (768568/56804575,300723/11360915,0,0,0),

of total1/25. Neither nonzero coordinate is as large as4/125, so the
third numerical slot cannot be placed. B is outside F_3(5,5), at exact
l1-distance

    3141314/284022875 > 0.                               (N8)

For completeness, distance to a branch with fixed prefix vector p is
2 sum_i(p_i-v_i)_+. The coordinates below p must be raised by that sum;
the same mass must be removed from the other coordinates. Since sum p<=1,
those other coordinates have sufficient slack, giving equality. Enumerating
all five or125 branch prefixes therefore gives the exact distances(N7)--(N8).
The closest prefix for B at depth3 is(1,0,1).

All leaf permutations preserve these domain distances. The consumer checks
all120 permutations, which includes the twelve S2 x S3 relabelings allowed
by the source groups. Neither witness can be approached by full slotwise
completions. Nor can a sequence of finite actual raw cap allocations tend
to either unit-total vector: completing each raw vector adds l1-mass equal
to its deficit from1, which would tend to zero. More quantitatively, if z
is any actual raw cap vector and delta is(N7) or(N8), then

    ||z-v||_1 + 1-sum_i z_i >= delta.

These statements concern allocated caps. They do not bound the true source
survivor above, and do not turn the absence of these two examples into a
positive uniform clipped estimate.

In particular, the same B-side response survives a different relaxed
allocation with a fully legal q5 slot sequence. Replace its q5 leaf vector
by(21/125,104/125,0,0,0): assign j=1 to leaf1, j=2 to leaf0, j=3 to leaf1,
and every j>=4 to leaf0. Keep all other star allocations and all other
mixed colours, except support{5,11,19}, mask37. Split that support's role
between(root1,leaf0) and(root1,leaf1), with the former weight1570657/2041125.
The common-colour polynomial then has exactly the original B response

    (0,0,0,397674116620058/4974836903276625,
             17363616113/178751640375).

An independent signed-matching recurrence verifies this equality. Numerical
slot realizations of its remaining fractional mixed allocations at
masks5,6,37 are not established by the tests in this report.
Thus the literal old tables are excluded,
whereas the B-side response and every associated template obstruction
have not been excluded. Root/leaf numerical-slot constraints for all mixed
supports remain essential.

## 5. A finite branch certificate remains possible with the whole tail

For fixed nonnegative leaf weights w summing to1, write R_l for the full
common-colour signed polynomial of Report793, and put

    F=sum_l w_l max(R_l,0).

On any product of branches(N3), choose fixed selectors0<=h_l<=1. Then

    F>=sum_l w_l h_l R_l.                                (N9)

The last expression is affine separately in each star allocation block
and each shared mixed-support allocation block. Its minimum on this product
of translated simplex cells is at a product of vertices. Thus certified
vertex lower bounds with fixed selectors establish a lower bound throughout
that cell. Different cells may use different fixed selectors. Alternatively,
the separately concave pair-deficit response of Report791 applies with
subprobability weights w_l h_l, reducing the mixed-colour calculation.

Neither method assumes that clipping preserves concavity. No complete
successful cell cover is asserted here.

There is also a quantitative finite approximation. Define

    Psi(S)=sum_(disjoint mixed-support collections I inside S)
             3^|I| b_(union I),   Psi(empty)=1.           (N10)

Empty collections are included; singleton supports are not event blocks.
For Q above, Psi(Q)=189181/80325. Since0<=m_ql<=1 and1<=c_Dl<=3,
termwise telescoping gives the absolute sensitivity bounds

    |partial R_l/partial m_ql| <= Psi(Q minus{q}),
    |partial R_l/partial c_Dl| <= b_D Psi(Q minus D).      (N11)

Two completions with the same retained root and leaf slots differ by at
most their remaining normalized mass in each marginal coordinate. The
two marginals contribute at most twice that amount. Consequently

    |F-F'| <= 2 sum_(q in Q)b_q epsilon_q Psi(Q minus{q})
               +2 sum_(|D|>=2)b_D epsilon_D Psi(Q minus D). (N12)

The same bound holds for every individual R_l. Positive clipping is
1-Lipschitz; weighting by a fixed probability adds no factor. All unexpanded
original heights are included in the epsilon terms.

## 6. Retaining actual numerical slots is much smaller than a height box

Retain the two full labels3n and9n whenever n<=N is a nonunit Q-smooth
integer. With support(n)=D, define

    epsilon_D(N)=1-(C_D/b_D)
                    sum_(support(n)=D,n<=N)1/n.

Then(N12) takes the single form

    delta_N=2 sum_(nonempty D subset Q)
        [b_D-C_D sum_(support(n)=D,n<=N)1/n] Psi(Q minus D). (N13)

Singleton supports in(N13) represent star sensitivity; larger supports
represent mixed-event sensitivity. The bracket is the exact full sum of
all omitted cap slots and is strictly positive at every finite cutoff.

| Numerical cutoff N | Retained nonternary n | Actual3n/9n slots | Complete uniform error delta_N |
| ---: | ---: | ---: | ---: |
| 1000000 |988|1976|0.00163186203...|
| 10000000 |2007|4014|0.000291090904...|
| 100000000 |3819|7638|0.0000491709977...|

These counts refer to retained numerical slots, not the much larger number
of possible colour assignments. The unchanged no3 mixed cap contribution
is still the full constant1 in c_Dl; it has not been omitted or reassigned.
Pure originals still determine the actual lambda_q laws.

For a finite calculation, fill omitted slots by designated colours to form
a reference polynomial value. This reference need not dominate the actual
family's unretained allocations and is not substituted for its physical
source. Compare it using(N13) with the dominating completion constructed
from the actual family. A uniform lower bound for every finite head
assignment, exceeding delta_N and the desired source threshold, would give
the corresponding all-height result. Establishing that lower bound is the
remaining obligation.

Here “all-height” refers only to the fixed seven nonternary axes under the
old ternary-depth-two hypothesis. Compact approximation does not guarantee
a positive uniform margin, a terminating finite certificate for every
family, or a decision procedure for Erdős#7. The infinite-slot closure can
touch zero even if each actual finite family separately has survivors.

## Verification and existing work

The [standalone numerical-slot consumer](../../../frontier/cover-geometry/refined-capped-source/numerical_slot_completion.py)
and [its result](../../../frontier/cover-geometry/refined-capped-source/numerical_slot_completion.json)
perform103785 exact rational
checks: the two membership failures, exact distances and all120 leaf
permutations for each;921 finite partially occupied root/leaf inventories;
the120 mixed-support depth-two cap sums; and6516 distinct numerical
d,3d,9d labels. The same consumer reconstructs B from the neighboring
Report796 certificate and independently verifies the repaired response
by a signed-matching recurrence. Normal and optimized Python reproduce
its result.

The [sparse-tail consumer](../../../frontier/cover-geometry/refined-capped-source/numerical_slot_tail_control.py)
and [its result](../../../frontier/cover-geometry/refined-capped-source/numerical_slot_tail_control.json)
contain seven exact numerical cutoffs, not a colour-assignment search.
An independent sparse-tail consumer generates smooth numbers by a
deduplicated minimum heap and computes Psi from set-partition counts,
separately from the producer's prime-recursion and support-packing
recurrences. It matches all seven retained numerical cutoffs and their
exact full-tail values, including the three rows above.

The underlying missing-label and first-layer principle is already used in
Report48's actual-source compatibility restrictions, Report305's effective
leading-label bounds, and Report782's fixed165 contribution10/11. Reports714
and789 explicitly allow the larger completed-simplex cap domain. The present
addition is the reusable slotwise-completion domain for that source response,
the exclusion of these two clipping witnesses, and its quantitative sparse
approximation over all nonternary heights. No literature-priority claim
is made.
