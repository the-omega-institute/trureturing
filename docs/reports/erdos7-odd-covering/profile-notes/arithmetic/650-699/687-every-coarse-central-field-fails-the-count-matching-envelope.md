# Every coarse central field fails the phase81 count-matching envelope

For [Report686](686-coherent-star-mode0-bound-and-complete-gate-counterexample.md)'s fixed phase81 family, weak corner(4,10), generic deep caps and FULL mode8 residual charges, the maximum corrected response-envelope gate over all coarse central fields0<=theta(c)<=1 is EXACTLY zero. The zero field attains it. Every field positive on an admissible source cell has a strictly negative gate.

This is a theorem about the declared count-matching response envelope and retention depending only on the central mod9/mod25 cell. It is not an impossibility theorem for outside-dependent or higher-digit-dependent retention, more precise query responses, other source constructions, or odd coverings. The actual101-original fixture remains noncovering. No new Lean verification is asserted.

## 1. Fixed input and admissible cells

Keep one actual globally fixed full residue at each of the101 numerical moduli in [clustered_global_phase_fixture.json](../../../frontier/cover-geometry/clustered_global_phase_fixture.json). In particular, each of the forty linear-star originals d*q, q in{7,11,13,17,19}, d in{3,5,15,9,25,45,75,225}, has central phase81 modulo d. Numerical labels and outside phases are unchanged.

The central null geometry is(3,5), with eighty live cells, and the fixed numerical weak corner is(4,10). Define the complete response table exactly as in686:

    r_q=1/(q-1), a_q=1/[q(q-2)],
    B7=157/210, Bq=1-rq-2aq for q>7,
    Zq(c)=max(0,Bq-rq*nq(c)),
    beta_pq=a_p*r_q+r_p*a_q+2r_p*r_q.

The six occurring count vectors are(n,n,n,n,n), with

    n=0,1,2,3,5,8;
    multiplicities30,26,12,6,5,1 respectively.

For n=0,1,2,3, all thirty-two matching responses are strictly positive. At n=5 or8, Z7=0. Those six cells have no positive-mass source in this construction and must be discarded. Set their entire response vector to zero. This is equivalent to requiring theta=0 there; arbitrary theta values on them have no effect. In particular, signed matching polynomials at inadmissible cells are not inserted into an optimization as if they were response probabilities.

There remain74 effective coordinates. On them the single actual outside source and all-height response bounds are exactly the ordinary construction established in686. No priority condition is imposed on the arbitrary field in this upper-bound argument: it covers the larger class of all coarse central fields, including any subclass that can also satisfy the required priority transport. The present result changes the field quantifier from one prescribed chi to EVERY central-cell field theta(c), keeping the response table fixed.

## 2. Complete field gate

Write mu(c) for the corner(4,10) weight, and define

    s_c=g*mu(c)*H_empty(c), g=200163067/201247200.

For each of the512 bundles b=(central_mode,T), let K_b be its full literal central selector menu, and let a_(b,k,c)>=0 be the selector's central cell coefficient multiplied by the SAME H_T(c). The complete gate is

    G(theta)=sum_c s_c theta_c
        -sum_b C_b max_(k in K_b)sum_c a_(b,k,c)theta_c.   (A1)

The field is fixed across all bundles and selectors. Each selector is fixed before summing over cells; there is no separate query choice per cell.

Use Report640's full coefficient array, with the four residual additions

    C_(8,{q}) += g/[q(q-2)], q=11,13,17,19.              (A2)

All original heights and the coefficient tails remain in these coefficients. No guarded mode9 shortcut is used. The559 central selector candidates are the full/root/leaf/deep tensor menus; normalized deep coefficients are1 at3 and4/5 at5, with no extra weak-leaf weight.

## 3. A reusable selector-mixture certificate

Suppose nonnegative rational numbers lambda_(b,k) satisfy

    sum_(k in K_b)lambda_(b,k)<=C_b                     (A3)

for every bundle. Since every selector reading is nonnegative for theta>=0,

    C_b max_k sum_c a_(b,k,c)theta_c
      >=sum_k lambda_(b,k)sum_c a_(b,k,c)theta_c.

Define one debit coefficient per cell,

    d_c=sum_(b,k)lambda_(b,k)a_(b,k,c).

Then the SAME gate obeys

    G(theta)<=sum_c(s_c-d_c)theta_c.                    (A4)

Thus pointwise inequalities d_c>=s_c imply G<=0 for every nonnegative field. This argument is homogeneous; the theorem for0<=theta<=1 is an immediate restriction. If d_c>=R s_c for every positive-source cell and R>1, then

    G(theta)<=-(R-1)sum_c s_c theta_c.                  (A5)

This is an ordinary finite linear comparison, not a reliance on an optimizer's dual status.

## 4. Reuse rational numbers, revalidate every current inequality

The pinned [Report682 candidate](../../../frontier/cover-geometry/clustered-q7-q11-retention-independent/clustered_q7_q11_retention_obstruction.json) contains2568 positive rational multipliers with denominator10^12 and addresses

    (mode,T,query7,query11,left_selector,right_selector).

Sum these NUMBERS over query7 and query11, retaining the exact current address(mode,T,left_selector,right_selector). This yields1733 nonzero coefficients lambda for(A3).

The old outside-root labels are not transplanted into a new source or reinterpreted as actual original phases. They only index contributions to a rational numerical schedule. Every resulting central selector is independently checked against the current literal menu. Every multiplier is applied to the CURRENT H_T(c), generic deep normalization and corrected coefficient array. All512 inequalities(A3) and all80 current cell inequalities(A4) are recomputed exactly. The earlier source law and its theorem are not premises of the new domination.

This is why collapsing the old labels is source-faithful: the final certificate has one fixed source/response table, one globally fixed original family and one valid mixture of whole-cell selectors in each CURRENT charged bundle. No averaging of separately attainable sources or choice of different original phases is involved.

## 5. Exact result and strict gap

Every current bundle budget(A3) passes. On the six discarded cells both s_c and d_c are zero. On all74 admissible cells d_c>s_c. The exact minimum ratio is

    R=min_(s_c>0)d_c/s_c
      =523631189695910122364169377659221
       /412988045678799323025011875000000
      =1.2679088297465233... ,                           (A6)

attained at root-major cell(5,14). Hence

    G(theta)<=-
      [110643144017110799339157502659221
       /412988045678799323025011875000000]
      sum_c s_c theta_c.                                (A7)

In particular, the simpler bound G(theta)<=-(1/4)sum_c s_c theta_c also holds. Any field retaining positive source mass has a negative envelope gate. The optimal value is zero, attained by theta=0; fields supported only on the six discarded cells are equivalent to it.

As a normalization regression, theta=1 on all74 admissible cells is686's original chi, and the verifier reproduces its complete gate

    -34684038567037034905564050721
     /275900078820714943795200000000.

Thus the conclusion strengthens686's one-policy failure to every coarse central-cell policy for THIS count-matching envelope. A weaker target such as merely a positive gate, or the inherited193/100000 threshold, cannot be reached in this class.

## 6. Runnable certificate and its boundary

The portable standard-library [verifier](../../../frontier/cover-geometry/clustered-q7-q11-retention-independent/coherent_star_allfields_obstruction_verify.py) and its [exact result](../../../frontier/cover-geometry/clustered-q7-q11-retention-independent/coherent_star_allfields_obstruction_verify.json) reconstruct the current model and certificate. The replay command is:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/clustered-q7-q11-retention-independent/coherent_star_allfields_obstruction_verify.py
```

It takes --directory(default: its own parent) and --output. Inputs are canonical files in the supplied directory; it imports no producer or temporary program and uses no optimizer. Run with Python -I -S -B -O. It checks8345 explicit predicates and writes the1733 exact dual weights, all512 fee budgets and all80 cell inequalities.

Input SHA256 values:

    remaining33_global_root_exclusion_certificate.json
      36e1be912a058df44a9ce3b13c89d97574620176b921e037568ceb96dd0f87d4
    clustered_global_phase_fixture.json
      4bc215b032c910224a3a23ed76edaf1e32dc8e243fe5ba474e129a1cee63e6b6
    clustered_q7_q11_retention_obstruction.json
      89b89676db47826d4c647692527da0656a1f6784d6d38feaca7081f1ad61c028


The separately authored [independent checker](../../../frontier/cover-geometry/clustered-q7-q11-retention-independent/coherent_star_allfields_obstruction_independent.py) and [result](../../../frontier/cover-geometry/clustered-q7-q11-retention-independent/coherent_star_allfields_obstruction_independent.json) pass55237 explicit checks. Without reading or importing the first verifier, it reconstructs cells in root-major order using the CRT formula, enumerates disjoint edge sets, rebuilds all559 selectors, and checks every current budget and residual against the supplied numerical result. It also reproduces all sixteen one-field fees and the exact strict ratio. Both canonical outputs replay byte for byte. These are independent implementations within the same model family, not independent model identities or Lean proofs.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/clustered-q7-q11-retention-independent/coherent_star_allfields_obstruction_independent.py
```

The necessary next change is outside this coarse-field class: a sharper response preserving actual root overlaps, a different actual source/kernel, or a proved richer retention interface. This certificate does not select which change will work. In particular it gives no upper bound on all outside-dependent fields and no arithmetic covering counterexample.
