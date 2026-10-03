# Fractional blocker packing is an exact finite relaxation of Section 243

Section 243 already gives the exact activation formulation

\[
 \Lambda_H=\min\left\{\sum_{v\in U}w_v:
   U\subseteq V_H,\quad
   \forall i\;\exists b\in N(i)\;T(i,b)\subseteq U\right\},
 \qquad w_v=p(v)-1,
\]

and rewrites it using inclusion-minimal blockers.  The existing inequalities
(243.3)--(243.4) are feasible packing certificates.  The finite cover/packing
duality in [FIB_SCALE_READOUT_PERMISSION_GEOMETRY.md, definitions 27.7--27.8](../../../../../develop/theory/FIB_SCALE_READOUT_PERMISSION_GEOMETRY.md#定义-277顶点的分数面边覆盖与最小覆盖概率)
can be reused after keeping the label index on each blocker.

Let
\[
 \mathcal R_H=\{(i,R): R\subseteq V_H\text{ is an inclusion-minimal set
 meeting every }T(i,b),\ b\in N(i)\}.
\]
The fractional blocker cover and its packing dual are
\[
 \Lambda_H^{\mathrm{frac}}=
 \min\left\{\sum_v w_vx_v:
      x_v\ge0,\quad
      \sum_{v\in R}x_v\ge1\ ((i,R)\in\mathcal R_H)\right\},
\tag{F243.1}
\]
\[
 \Lambda_H^{\mathrm{pack}}=
 \max\left\{\sum_{(i,R)\in\mathcal R_H}\alpha_{i,R}:
      \alpha_{i,R}\ge0,\quad
      \sum_{(i,R):v\in R}\alpha_{i,R}\le w_v\ (v\in V_H)\right\}.
\tag{F243.2}
\]

This is a finite rational LP pair.  Its incidence matrix is the blocker
incidence matrix and its right-hand sides are integral, so finite LP strong
duality and rational vertex attainment give
\[
 \Lambda_H^{\mathrm{frac}}=\Lambda_H^{\mathrm{pack}}
 \le \Lambda_H.
\tag{F243.3}
\]
The last inequality is the integrality relaxation: the integer value in §243
restricts \(x_v\) to \(0/1\).  The label index is retained in (F243.2), even
when two labels have the same blocker set, because the two constraints are
separate and their packing mass shares the same coordinate capacities.

The relaxation can be strict.  On \(V=\{0,1,2\}\), take one label with
activation options \(\{0,1\},\{0,2\},\{1,2\}\) and unit coordinate weights.
Its minimal blockers are the same three pairs.  The integral activation value
is \(\Lambda_H=2\), while assigning \(x_0=x_1=x_2=1/2\) gives
\[
 \Lambda_H^{\mathrm{frac}}=\Lambda_H^{\mathrm{pack}}=3/2,
 \qquad \Lambda_H/\Lambda_H^{\mathrm{frac}}=4/3.
\]
Thus an optimized packing is a certified lower bound, not an equality for the
0/1 activation cost and not a replacement for the source-global liability.

The exact verifier
[`verify_blocker_fractional_duality.py`](../../../frontier/cover-geometry/blocker-fractional-duality/verify_blocker_fractional_duality.py)
uses rational Gaussian elimination and vertex enumeration.  It checks 67,475
weighted finite systems exhaustively for universes of size at most three,
plus 11 deterministic representatives at sizes four and five.  It reports
`PASS`, checks primal value = dual value and fractional value \(\le\) integral
value in every case, and records the triangle gap above.  The audit does not
produce blocker weights with total larger than \(\mathcal B_H\), does not
check the whole-owner strata constraints (243.5)--(243.9), and does not settle
whole-cover noncoverage or Erdős #7.
