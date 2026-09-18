[Index](../marked_head_profile.md) · [Generic tied-root bridge](99-tied-root-deep-payments-use-one-actual-capacity-budget.md) · [One-residual consumption](100-fractional-deep-payments-improve-the-global-comparison.md)

# One root-imbalance charge reduces the deep-capacity penalty

The deep-capacity coefficient C in99 can be replaced by

    kappa=max(36*vmax/125,36*(vmax-vmin)/25),      (RI0)

without increasing its existing root-imbalance coefficient. The
ordinary bridge, valid on the full source slab Delta<=1/18, is

    Q_D-P_D>=-kappa*E_D-sigma_D*C*chi.            (RI1)

The improvement comes from grouping both root0 cells before paying
their imbalance. Their combined selected-label mass is at most
sigma_D, so this payment does not require a second copy of that
coefficient. The remaining deep-capacity charge uses only the
derivative range and the missing ternary mass. The same result
applies to all41 original linear and five quadratic costs, with
every independent original layout and complete infinite tail.

Under99's additional concentration and source-packing guards,
the marked-cost interface becomes

    d_i_actual>=m_i_old+
        [g_i-P_i*(rho-r/5)-Q_i*chi]_+,
    g_i=vmin_i*min(((1-delta)/5)*G,m/5),
    P_i=max(vmax_i,36*(vmax_i-vmin_i)/25,
                                      vmin_i*m/G),
    Q_i=sigma_(D,i)*C_i.                         (RI2)

Thus g and Q are unchanged and P decreases or stays equal. This
coefficient interface alone does not assert a new global K. These
are ordinary proofs with exact rational checks, not Lean results.

## 1. Keep the two parts of each actual capacity defect

Use99's notation, including the original independent baselines b,c5,
v_l=f(b_l+1)-f(b_l), k_l=C-f(b_l), z_l=k_l*d_l-c5_l*v_l/5, and

    s_shift=max_l(z_l+v_l/5)-max_l z_l.

The increasing discretely convex costs have

    0<vmin<=v_l<=vmax, C>=f(3)+3*vmax,
    0<=s_shift<=vmax/5.

For every original selected label3^a*7^e, write A for its actual
old ternary cylinder, L=3^-a and u_e=6/(5*7^e). Keep all e>=1.
For a nonempty A in surviving ternary cell l, the two nonnegative
pieces of its capacity defect are

    D_missing=d_star*(L-eta(A)),
    D_cell=(d_star-d_l)*eta(A),
    d_star*L-Lambda(A)>=D_missing+D_cell.         (RI3)

Its contribution to P_D-Q_D is exactly

    u_e*[s_shift*(L-eta(A))
                   +(s_shift-v_l/5)*eta(A)].     (RI4)

The first term is at most

    (36*vmax/125)*D_missing,                     (RI5)

since d_star>=25/36. This applies in both roots.

For a root1 label the second term is at most

    ((vmax-v_l)/5)*eta(A)
      <=((vmax-vmin)/5)*eta(A)
      <=(36*(vmax-vmin)/25)*D_cell,               (RI6)

using d_star-d_l>=5/36. Equations(RI5)--(RI6) are charged to the
two different nonnegative pieces of the same defect. Their sum is
at most kappa*(D_missing+D_cell); adding their coefficients is
unnecessary.

## 2. Both root0 cells share one imbalance mass

For either root0 cell l, tie d0 and d1 by raising the smaller
coordinate to d_star. If l is nonmaximal, raise l itself; if l is
maximal, raise the other root0 cell. The increase in its z coordinate
is at most C*chi, where chi=|d0-d1|.

The shift function is1-Lipschitz under a single-coordinate increase,
and99's generic tied-root lemma applies after this change. Hence for
either original root0 cell,

    (s_shift-v_l/5)_+<=C*chi.                    (RI7)

This includes equal root values, when the right side is zero. The
tied-root lemma covers all ten baselines, including nonnested root
and cell labels, and every independent c5. No compatibility between
the original labels has been introduced.

Let I0 be the single set of selected original labels whose nonempty
surviving cylinders lie in either root0 cell. Every label belongs to
at most one of the two cells. Therefore

    sum_((a,e) in I0)u_e*eta(A_(a,e))
      <=sum_(a=3..k,e>=1)u_e*3^-a=sigma_D,        (RI8)

where k=5 for linear costs and k=6 for quadratic costs. This is one
sum over the union, not two separately bounded sums. Equations
(RI7)--(RI8) pay the entire second term of(RI4) on root0 with the
single charge sigma_D*C*chi. The first term still uses(RI5).

Empty labels and cylinders in removed cells have zero eta and
Lambda mass, so their full defect is paid by(RI5). Summing(RI4)
over the root0 and root1 partition, using(RI3), proves(RI1).
Absolute convergence follows from the same complete weights as99.
The coefficients remain

    sigma_D=13/1215 (linear), 8/729 (quadratic),
    remaining pure3 mass=1/2430 or1/7290,
    sigma_D+remaining mass=1/90.                 (RI9)

All depths and all original residues are retained. No claim that
different deep labels share a ternary carrier is used.

## 3. Insert the smaller coefficient before the one-budget estimate

The actual source-hole identity99(TD11), its retained quadratic
curvature and the complete source payments are unchanged. It gives
the same marked credit, now bounded below by

    vmin*((1-delta)/5)*x_J+V5(v*I_J)
                   -kappa*E_D-vmax*omega-Q*chi.  (RI10)

The actual unused-capacity and union errors still satisfy

    E_D+(E5-r/5)+omega<=rho-r/5.                 (RI11)

At the best slot H,99's nonnegative-product bound pays the missing
cofactor5 labels with coefficient vmin*m/G. At another slot the
source hole is at least G, so the V5 term can be dropped. Taking
the maximum of the three error coefficients gives

    max(kappa,vmax,vmin*m/G)
      =max(vmax,36*(vmax-vmin)/25,vmin*m/G),      (RI12)

because36*vmax/125<=vmax. The same two-slot argument and the old
unimproved cost bound now give(RI2). Each cost uses the same actual
rho; the equation does not authorize summing independent copies
of this budget. Since chi<=sigma_escape/4, a global consumer may
charge Q/4 to the existing source-escape coefficient as in100.

For99's fixed lower packing gap G_star, the exported uniform form is

    g_i=vmin_i*min((1-delta)*G_star/5,
                                    1/50-r_star/5),
    P_i=max(vmax_i,36*(vmax_i-vmin_i)/25,
                                     vmin_i/(9*G_star)),
    Q_i=sigma_(D,i)*C_i.                         (RI13)

The cutoff0<=r<=r_star is inclusive. All four packing guards, the
concentration condition and Delta<=1/18 remain required. Since
C>=3*vmax, both kappa and vmax are at most C, so(RI13) never has
a larger residual coefficient than99's uniform interface. The
coefficients g and Q agree exactly.

The strengthened bound replaces99's estimate on the same marked
credit. A consumer uses the maximum or valid convex combinations
of alternative bounds for each original cost. It cannot add their
full gains. All signed old coefficients, the original curvature,
remaining tails and later comparison branches must still be kept.

## 4. Exact interface and verification

[shared_root_imbalance_payment.py](../frontier/shared_root_imbalance_payment.py)
exports `uniform_coefficients(cost_rows, delta, rcut)` with the same
g,P,Q interface as99. Its rows also give the two local payment
coefficients, kappa, the previous P and the exact penalty reduction.
The [certificate](../certificates/source_norms/shared_root_imbalance_payment.json)
uses schema `erdos7-shared-root-imbalance-payment-v1`.

The checker revalidates99's generic nonnested tied-root cone,4600
original cost/layout pairs,365 source increments and23000 floors.
For every46 costs it checks the two exact geometric payment
identities, all complete selected/unselected tail coefficients,
and equality of the old and new g,Q with P no larger. The proof
of the single root0 mass bound is(RI8); the finite certificate does
not purport to enumerate the infinite family.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/shared_root_imbalance_payment.py --output docs/reports/erdos7-odd-covering/certificates/source_norms/shared_root_imbalance_payment.json
python3 -I -O docs/reports/erdos7-odd-covering/frontier/shared_root_imbalance_payment.py --check
```

Any global K improvement requires a separate complete consumer.
Unrestricted Erdos #7 and arbitrary later-prime continuation remain
open.
