# A constant four-root response box cannot pay the complete gate

Replacing the actual active-root and pair patterns by their separate worst values loses too much joint information in the following proposed comparison. Its matching polynomial is strictly positive, but no retention field bounded by one can pay the public gate193/100000. This excludes the specified constant comparison table, not an actual coherent phase family, an exact avoidance source, or a mixture of ordered conditional kernels. It gives no covering counterexample.

The distinction matters when trying to remove [673's fifty retained incidence conditions](673-heterogeneous-fields-complete-the-live-leaf45-role-domain.md). A source-existence bound must also control the full set of queries from that same source. Positive source mass alone does not supply the required net gate.

## 1. The proposed uniform comparison

Fix Q={7,11,13,17,19}, r_q=1/(q-1), and a_q=1/[q(q-2)]. Assume a comparison has charged up to four distinct live first roots at each coordinate, all three square prefixes at7, and two square prefixes at each q>7. Its uniform unary lower values are

    Z7=26/105, Z11=287/495, Z13=280/429,
    Z17=757/1020, Z19=2243/2907.                  (F1)

Also charge, on every pair{p,q}, both square-pair orientations and two root-pair events, using

    beta_pq=a_p r_q+r_p a_q+2r_p r_q.           (F2)

This is an envelope: the original central congruences determine which deletions are actually active, and those patterns need not realize all these maxima simultaneously. Numerical moduli and original phases have not been constructed to realize this constant table.

For each outside query support T, take the induced matching polynomial

    H_T=sum_(matching M in Q\T) (-1)^|M|
          product_(e in M) beta_e
          product_(q in (Q\T)\V(M)) Z_q.       (F3)

Exact arithmetic gives

    sum_(p<q) beta_pq/(Z_p Z_q)
      =12120375130167/14190523605440 <1,
    H_empty=1413576886723/132229083987000 >0.   (F4)

All32 induced responses are positive. The obstruction below accepts these response values as its premise; it does not dispute the strict matching region or assert that all actual sources have these response values.

## 2. The whole-coordinate queries already give an upper obstruction

Use [640's complete512 coefficients](640-global-root-exclusions-close-the-complete-core-inventory.md), g=200163067/201247200, and the four guarded9q² additions at central mode9 from the later head interface. The additions do not affect mode0. Write C_(m,T) for these nonnegative coefficients.

At weak corner(i,j)=(4,6), retain the old nulls3,5 and central15 mask. Let w_l be1/9 at l=4 and2/9 at the other live ternary leaves; let v_m be3/75 at m=6 and4/75 at the other live quinary leaves. Then

    D=sum_(live unmasked l,m) w_l v_m=37/45.   (F5)

For an arbitrary field0<=theta(l,m)<=1, put

    M_theta=sum_(live unmasked l,m) w_l v_m theta(l,m).

Mode0 has one central selector: the entire central source. Because every H_T inF3 is constant across the central cells, its source contribution and all32 mode0 fees have the same factor M_theta. Every other central mode has a nonnegative fee. Thus the complete gate satisfies

    G(theta)<=A M_theta,
    A=g H_empty-sum_T C_(0,T) H_T
     =8482754828806680432735281
       /3678667717609532583936000000 >0.       (F6)

Since M_theta<=D, this gives the exact uniform upper bound

    G(theta)<=A D
     =313861928665847176011205397
       /165540047292428966277120000000
     =0.0018959879122869006... <193/100000.     (F7)

The exact shortfall is

    5630362608540728903636203
      /165540047292428966277120000000.         (F8)

The argument allows an arbitrary field at this one corner, even without either weak-marker priority. It therefore excludes every whole95 priority family for this constant response table, any finite library of such families, and any convex mixture that keeps the same response table. Adding more candidate fields cannot repairF7. Ignoring the other nonnegative fees strengthens the upper bound argument; those fees have not been omitted from a claimed positive certificate.

## 3. What information must be restored

The obstruction is in the replacement of cell-dependent joint responses byF1--F3. It does not show that the actual globally fixed phases realize a bad gate, and it does not rule out the original phase family having survivors. It also does not exclude a construction that changes the response table, such as exact conflict restriction, a mixture of ordered conditional sources, or a comparison that preserves which central cells share each original activation.

A next positive result must retain enough common information to improve the coupled mass/query response. A separate positive lower bound on raw survivor mass, the positivity inF4, or optimization of theta against the unchanged table cannot supply that missing inequality. Even after the fifty incidence conditions are removed, arbitrary low-pure/null geometry and the unrestricted continuation-parent problem remain independent obligations.

The [exact program](../../frontier/cover-geometry/four_root_uniform_box_gate_obstruction.py) reconstructs every matching response and pins the complete fee input. Its [result](../../frontier/cover-geometry/four_root_uniform_box_gate_obstruction.json) recordsF1--F8 and all512 coefficients. The field-universal implication is the ordinary proofF5--F7; no finite enumeration of candidate fields is used in that implication. No new Lean verification is claimed.

The program passes45 explicit checks. A separately authored [independent computation](../../frontier/cover-geometry/uniform_four_root_box_mode0_obstruction.py) passes1,081 checks and [reproduces the same upper bound and shortfall](../../frontier/cover-geometry/uniform_four_root_box_mode0_obstruction.json). It also checks all1,024 event-induced matching polynomials, whose minimum normalized value is1413576886723/7095261802720>0. This corroborates that the displayed obstruction concerns the paid gate, rather than a failure of matching positivity. Both computations use the same agent/model family.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/four_root_uniform_box_gate_obstruction.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/uniform_four_root_box_mode0_obstruction.py
```
