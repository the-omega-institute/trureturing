# Five-parent unit-cost hinge budgets exceed the guaranteed head reserve

For the same fixed parent set `{3,5,7,11,13}` at owners `37,41,43`, the direct completed-count hinge comparison from [Report651](651-an-unqueried-head-coordinate-admits-four-parents-from-thirty-seven.md) has total minimum debit

$$
0.011444857391085747\ldots
>
\gamma_{20}
=\frac{203129722400814193208791597}
{20692505911553620784640000000}
=0.009816583997561991\ldots.
$$

Here $\gamma_{20}$ is the **guaranteed head reserve** supplied by [Report648](648-induced-pair-responses-release-all-square-pairs.md). The inequality holds for every finite unit-cost selection of nonunit cofactor patterns and every admissible real row parameter $h\ge12$, with the completed-count comparison and auxiliary envelopes specified below. It prevents this additive sufficient budget from closing against that guaranteed reserve. It is not a lower bound on actual violation mass, an upper bound on actual head mass, or a counterexample to five-parent noncoverage.

The same parent set is admissible at all three owners. No separately optimized actual sources or incompatible parent sets are combined. This is ordinary mathematics with exact rational certificates, not new Lean verification.

## 1. The fixed source interface and the comparison debit

Use the actual head source and original phase conventions of Report648. All numerical originals and parent unions are fixed globally. At every relevant outside owner, use one threshold row fixed before sampling histories, with density cap

$$
c_v=\frac{v-1}{h}<\frac v{12}.
$$

Rows are normalized on every complete prior history, including dead fibres. Conditional query caps and backward integration are those of Report651; the stricter $h\ge12$ invariant is a hypothesis of this result.

For the critical parent set, introduce independent auxiliary depths $L_i$, indexed by

$$
p=(3,5,7,11,13),\qquad
k(1)=\left(\frac23,\frac4{15},\frac16,\frac1{10},\frac1{12}\right),
$$

$$
\Pr(L_i\ge0)=1,\qquad \Pr(L_i\ge1)=k_i(1),\qquad
\Pr(L_i\ge e)=d_i p_i^{-e}\quad(e\ge2),\qquad
d=\left(2,\frac43,\frac75,\frac{11}9,\frac{13}{11}\right).
$$

Their independence evaluates a reference kernel; it does not assert independence of the actual surviving coordinates. Put

$$
C_0=\prod_{i=1}^5(L_i+1)-1.
$$

The unit pattern is already paid by the ordinary domain. The complete infinite first moment is

$$
\mathbb E C_0
=\prod_i\left(1+k_i(1)+\frac{d_i}{p_i(p_i-1)}\right)-1
=\frac{95}{33}.
$$

Coordinates 17 and 19 are absent from the fixed parent set. Their actual unary source masses supply

$$
\zeta=Z_{17}Z_{19}=\frac{4138163}{4744224},\qquad
Z_q=\frac{q-2}{q-1}-\frac{2}{q(q-2)}.
$$

To preserve this factor, first integrate normalized later kernels backwards, using their full-history conditional caps at queried coordinates. Once those kernels are gone, the remaining payoff is independent of the omitted core coordinates. Integrate their actual unary factors before dropping the other deletion restrictions. This is Report651's conditional increasing-convex comparison applied to both omitted coordinates. It neither normalizes the restricted head nor multiplies an unrelated event bound by its total mass.

For no preselection, define

$$
B_\varnothing(v,h)
=\frac\zeta h\,
\mathbb E\bigl(C_0-(v-3-h)\bigr)_+,
\qquad 12\le h\le v-3.
\tag{F1}
$$

The actual violation mass is bounded **above** by this prescribed comparison debit. A lower bound on the debit is not a lower bound on that violation mass. Completing missing patterns and all positive owner heights is permitted only on this upper-comparison side; globally fixed original phases remain unchanged during the conditional comparison.

## 2. Arbitrary unit-cost preselection cannot reduce the debit

Let $S$ be any fixed finite set of $N$ distinct nonunit cofactor exponent patterns. It need not be a prefix, box or smooth ordering. For an auxiliary depth vector $L$, let

$$
m_S(L)=\#\{s\in S:s_i\le L_i\text{ for every }i\},\qquad
C_S=C_0-m_S(L),\qquad D_S=v-3-N.
$$

[Report647](647-order-matched-moments-strengthen-complete-networks.md), (OM3) and (OM7), supply this unit-per-selected-pattern domain/count interface. For $12\le h\le D_S$, the same direct hinge construction gives

$$
B_S(v,h)=\frac\zeta h\,
\mathbb E\bigl(C_S-(D_S-h)\bigr)_+.
\tag{F2}
$$

Since $0\le m_S(L)\le N$, pointwise

$$
C_S-(D_S-h)
=C_0-(v-3-h)+N-m_S(L)
\ge C_0-(v-3-h).
$$

Monotonicity of the positive part therefore yields

$$
B_S(v,h)\ge B_\varnothing(v,h).
\tag{F3}
$$

Moreover, $[12,D_S]\subseteq[12,v-3]$. Thus the unselected expression gives a lower bound on every admissible selected-set debit, even if each owner is allowed its own set $S$ and its own real $h$. An empty feasible interval contributes no admissible row. This conclusion is an algebraic consequence of the existing domain/count formulas and hinge monotonicity; no enumeration of selected sets is needed.

The argument uses a uniform unit charge for every selected nonunit pattern. It does not apply unchanged to exact remaining-domain costs, probability-weighted pattern costs, a completion that retains missing-label information, different source envelopes, or different row constraints.

## 3. Exact minima over all admissible real row parameters

Set $D=v-3$. Because $C_0$ is integer-valued, the function

$$
h\longmapsto\mathbb E(C_0-D+h)_+
$$

is affine between consecutive integer values of $h$. On each such interval, division by the positive $h$ gives a function $a/h+b$, which is monotone or constant. Consequently the minimum of (F1) over the closed real interval $[12,D]$ occurs at an integer endpoint. The endpoint $h=D$ is included; its threshold is zero and the row remains admissible.

The exact finite computation uses

$$
\mathbb E(C_0-t)_+
=\mathbb E C_0-t+\mathbb E(t-C_0)_+.
\tag{F4}
$$

Writing $M=C_0+1$, the negative part has support $M\le t$. Thus only a finite hyperbolic cross is enumerated, while the exact first moment retains the complete infinite positive tail. There is no cutoff on original exponent heights.

| Owner $v$ | Minimizing $h$ | Exact comparison debit, decimal display |
|---:|---:|---:|
|37|12|$0.004980701579584181\ldots$|
|41|15|$0.003485376150446660\ldots$|
|43|12|$0.002978779661054904\ldots$|

The rational certificate verifies the stronger exact comparison

$$
\sum_{v\in\{37,41,43\}}\min_{12\le h\le v-3}B_\varnothing(v,h)
>\frac{2861}{250000}>\gamma_{20}.
\tag{F5}
$$

The exact sum exceeds $\gamma_{20}$ by $0.001628273393523755\ldots$. Combining (F3) and (F5) proves the stated obstruction for arbitrary unit-cost selections and all admissible real $h\ge12$, before any further nonnegative debit is added. This proves no simultaneous attainment of the auxiliary upper bounds by actual phases.

## 4. Localization among the five-parent comparison types

The auxiliary comparison can also separate exact membership in

$$
\{3,5\},\qquad Q=\{7,11,13,17,19\},\qquad\{23,29,31\},
$$

and the number $k$ of outside parents. There are

$$
\sum_{j=0}^5\binom{10}{j}=638
$$

head-subset/outside-count types. These classify comparison envelopes, not all actual sources, histories or phases. Sorted outside parents are bounded below by the corresponding entries of $(37,41,43,47,53)$ and must precede the owner. The eligible type counts at 37, 41, 43 are respectively 252, 462, 582.

For 23, 29, 31, the conditional caps are $k_p(e)=c_p/p^e$ with $c_p=5/3,20/11,2$. The $j$th outside reference $u_j$ has

$$
k_j(1)=\frac1{12},\qquad
k_j(e)=\frac1{12}u_j^{1-e}\quad(e\ge2).
$$

The same actual row invariant supplies these outside envelopes. For omitted $q\in Q$, multiply the uniform source factors $Z_7=5/6$ and the $Z_q$ above. If neither 3 nor 5 is queried, retain also the central 15 mask factor $14/15$: under the central product source, the relevant root masses are at least $1/3$ and $1/5$, so the deleted root rectangle has mass at least $1/15$. Omitted-coordinate factors are bounded uniformly before integrating this mask.

For each prime owner from 37 through 113, minimize the largest type debit using one common $h$. Every selected common row is controlled by the same parent set `{3,5,7,11,13}`. At the first three owners the common-row values equal the fixed-parent minima in §3. The group maxima at the first two common rows are:

| Parent membership | Owner 37, $h=12$ | Owner 41, $h=15$ |
|---|---:|---:|
|Both 3 and 5|$0.00498070\ldots$|$0.00348537\ldots$|
|3 only|$0.00144162\ldots$|$0.000992867\ldots$|
|5 only|$0.000298643\ldots$|$0.000197995\ldots$|
|Neither|$0.0000491938\ldots$|$0.0000313911\ldots$|

The all-$Q$ type itself costs only $0.0000455826\ldots$ and $0.0000278537\ldots$ at those rows. Thus querying every coordinate of $Q$, and thereby losing all omitted-$Q$ factors, is not the controlling difficulty in these comparisons. At 41, some noncontrolling groups are maximized by a type containing outside parent 37. Separating these roles is necessary for the stated localization.

## 5. Exact artifacts and remaining boundary

The [producer](../../frontier/cover-geometry/five_parent_branch_hinge_certificate.py) and its [rational data](../../frontier/cover-geometry/five_parent_branch_hinge_certificate.json) evaluate the full first moment and the finite negative part by Dirichlet convolution. The [independent verifier](../../frontier/cover-geometry/five_parent_hinge_independent.py) and its [result](../../frontier/cover-geometry/five_parent_hinge_independent.json) use direct hyperbolic-cross recursion, without importing the producer. They agree on all 79 integer endpoints for the fixed-parent minima, their exact sum, and the strict comparison with the guaranteed reserve. The real-parameter and arbitrary-selection reductions are the proofs in §§2–3.

The producer passes 125761 explicit checks; the independent verifier passes 183. Reproduce from the repository root, including with Python assertions disabled:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/five_parent_branch_hinge_certificate.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/five_parent_hinge_independent.py
```

The fixed-parent obstruction concerns the completed cofactor count, these auxiliary envelopes and omitted-coordinate factors, the unit cost per selected pattern, the $h\ge12$ invariant, and the stated guaranteed reserve. A sharper joint response retaining the queried 3/5 structure, a stronger guaranteed head reserve, or a more informative domain/count representation is outside this obstruction. No upper bound on the head mass, lower bound on actual loss, covering family, or impossibility of a five-parent survivor theorem follows from it.
