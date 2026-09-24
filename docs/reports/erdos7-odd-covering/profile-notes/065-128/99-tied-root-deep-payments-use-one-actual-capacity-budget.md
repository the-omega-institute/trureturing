[Index](../../marked_head_profile.md) · [Actual source packing](85-a-broad-five-slot-source-deletion-tradeoff.md) · [Selected deep capacity](91-cell-vector-markers-retain-the-selected-deep-deletion.md) · [All46 marked source payments](94-quadratic-marked-events-and-a-common-residual-improve-global-k.md)

# Tied-root deep payments use one actual capacity budget

For all41 original linear costs and all five original quadratic costs,
the fixed selected-deep loss can be replaced by the actual unused deep
capacity and one explicit root imbalance. This deep-capacity bridge
is valid on the whole source slab Delta<=1/18, including all ten
original root/cell baselines and every independent second layout.
Under the additional concentration and source-packing guards of
(TD12) and(TD17), it gives the positive-credit coefficient interface

    d_i_actual>=m_i_old+
      [g_i-P_i*(rho-r/5)-Q_i*chi]_+,               (TD0)

where chi=|beta0-beta1|. Every g_i is positive at94's fixed concentration
parameters. This replaces a bound on the same marked credit; it is not
an extra gain to add to94's gain. The resulting coefficients alone do
not assert a new global K bound. All infinite tails, the actual common
source measures and the original quadratic curvature are retained.
The proof is ordinary mathematics with exact rational checks, not Lean
verification or a solution of unrestricted Erdos #7.

## 1. A generic tied-root comparison includes nonnested labels

Let ROOT=(0,0,1,1,1), and let

    b_l=1+I_ROOT(l)=R+I_l=j,
    R in{0,1}, j in{0,1,2,3,4}.

All ten choices are allowed. In particular, j need not lie in root R.
Let c5 be an independently chosen member of the same ten-element
family. More generally the argument below only needs1<=c5_l<=3.
For a nonnegative increasing discretely convex cost f, write

    Delta_a=f(a+1)-f(a), 0<=Delta_1<=Delta_2<=Delta_3,
    v_l=Delta_(b_l), k_l=C-f(b_l), t_l=c5_l*v_l,
    C>=f(3)+3*Delta_3,
    z_l=k_l*d_l-t_l/5,
    y_l=z_l+v_l/5,
    s_shift=max_l y_l-max_l z_l.                  (TD1)

Suppose d0=d1=q>=25/36 and0<=d_j<=5/9 for j>=2. Then

    0<=s_shift<=min(v0,v1)/5.                     (TD2)

It suffices to find a maximizer of y whose derivative is at most
min(v0,v1): its own unshifted entry is a candidate for max z.
The two root0 baselines are equal or adjacent, and their minimum m
is1 or2. If they differ, the lower-baseline cell l and the higher cell h
satisfy

    y_l-y_h
      =q*Delta_m-(c5_l-1)*Delta_m/5
                    +(c5_h-1)*Delta_(m+1)/5
      >=(q-2/5)*Delta_m>=0.                      (TD3)

If m=2, every root1 baseline is at most2, including the nonnested
case R=0,j>=2. Thus all remaining candidates have derivative at most
Delta_m. If m=1, every unsafe root1 candidate has baseline at least2.
The chosen root0 baseline1 cell obeys

    y_l>=q*(C-f(1))-2*Delta_1/5,
    y_j<=(5/9)*(C-f(2)),
    y_l-y_j>=(q-5/9)*(C-f(1))
                         +(5/9-2/5)*Delta_1>=0.  (TD4)

Here k_j>=0 and f(b_j)>=f(2) justify the upper bound for root1.
This includes the nonnested case R=1,j<2. Equations(TD3)--(TD4)
prove(TD2) for all ten baselines and every independent c5.

The exact checker also verifies these comparisons on the full cone

    (f(1), Delta_1, Delta_2-Delta_1,
               Delta_3-Delta_2, C-f(3)-3*Delta_3)>=0.

It evaluates the five generating rays for each unsafe comparison of
all100 layout pairs. Increasing q above25/36 improves those comparisons;
decreasing a root1 availability below5/9 also improves them because
k_j>=0. Every original cost is then reconstructed in these coordinates.
Thus the calculation checks a general low-cost cone as well as4600
original cost/layout pairs; it does not replace the proof by sampling
the source domain.

## 2. Actual deep defects pay the complete selected family

Use the actual source parameters of48 and85, and write

    z=3/4+p, alpha1=1/4-a,
    beta2+beta3+beta4=1/4-b,
    Delta=p+a+b<=1/18.

Their simplex constraints give alpha0<=a and beta0+beta1<=b. Hence

    d0,d1>=3/4-a-b>=25/36,
    d_j=1/2+p+a-beta_j<=5/9 (j>=2),
    d_star=max(d0,d1)=max_l d_l,
    d_star-d_j>=5/36 (j>=2),
    chi=|d0-d1|=|beta0-beta1|<=b.                 (TD5)

For a linear cost select k=5 pure3 cofactors, and for a quadratic cost
select k=6, exactly as in94. Define

    alpha=k/5,
    sigma_D=(1/5)*sum_(a=3..k)3^-a
      =13/1215 (linear), 8/729 (quadratic).

For each original label3^a*7^e, a=3,...,k and e>=1, let A_(a,e) be
its actual old-coordinate ternary cylinder; an absent label is empty.
Keep its actual residue independently at every depth. The complete
seven weights are

    u_e=6/(5*7^e), sum_(e>=1)u_e=1/5.

Let eta be the actual restricted ternary source measure,
M=eta tensor Haar5, and0<=Lambda<=M the actual source measure. With
q_D=sum_(a,e)u_e*I_(A_(a,e)), define

    V_D=q_D*Lambda,
    E_D=sigma_D*d_star-V_D(1)>=0,
    Q_D=integral_(F_J) v*q_D dM,
    P_D=sigma_D*s_shift.                         (TD6)

The marked five-slot F_J is an independent original test residue.
Since v and q_D depend only on the ternary coordinate, the product
identity gives Q_D=sum_(a,e)u_e*v_l*eta(A_(a,e))/5. Each nonempty
deep cylinder belongs to one surviving ternary cell l. Put L=3^-a.
Its capacity defect obeys

    d_star*L-Lambda(A)
      >=d_star*(L-eta(A))
                     +(d_star-d_l)*eta(A),       (TD7)

because eta(A)<=L and Lambda(A)<=d_l*eta(A). Its contribution to
P_D-Q_D is

    u_e*[s_shift*(L-eta(A))
                   +(s_shift-v_l/5)*eta(A)].     (TD8)

The first term is paid by the first summand of(TD7) with coefficient
at most36*vmax/125, since s_shift<=vmax/5 and d_star>=25/36.
For a root1 label, the positive part of the second term is paid by
the second summand of(TD7) with coefficient36*vmax/25. Both
coefficients are at most C, since C>=3*vmax.

For a nonmaximal root0 label, raise its d_l to d_star. This changes
only z_l, by k_l*(d_star-d_l). The function

    z -> max(z+v/5)-max(z)

is1-Lipschitz when a single coordinate is increased: each maximum
increases by a number in[0,t], so their difference changes in[-t,t].
At the tied value(TD2) applies. Consequently

    (s_shift-v_l/5)_+
      <=k_l*(d_star-d_l)<=C*(d_star-d_l),         (TD9)

and(TD7) pays this case as well. For a maximal root0 label, instead
raise the other root cell to d_star. The same argument leaves at
most C*chi. Its total weighted ternary mass is at most sigma_D,
so the additional charge is at most sigma_D*C*chi.

Empty labels or cylinders in removed cells have eta(A)=Lambda(A)=0
and their full capacity defect. The first payment covers them.
All series converge absolutely: their terms are bounded by fixed
cost coefficients times u_e*3^-a. Summing(TD7)--(TD9), with every
e>=1 retained, proves

    Q_D-P_D>=-C*E_D-sigma_D*C*chi.                (TD10)

The unselected complete pure3 mass tail is1/2430 for linear costs
and1/7290 for quadratic costs. In both cases sigma_D plus this tail
is1/90, the original complete deep mass coefficient. These are mass
coefficients with the outer1/5 included; the cost coefficients before
that factor are the ones appearing in94. Thus no infinite tail is
discarded or replaced by a finite cutoff.

## 3. Source-hole cancellation uses no second payment

Let W=M-Lambda>=0 and q_sh=v3+v9 be the actual complete shallow
virtual density. Keep the source payment alpha*integral_(F_J)v dW,
the original quadratic curvature and the independent15/45 test
payments exactly as in94. The selected floor changes t to t-v and
retains the actual marked deletion integral; its old shallow shift is

    P_sh=integral_(F_J) v*q_sh dM.

The following is an identity for these same actual measures:

    alpha*integral_(F_J)v dW
       +V_sh(v*I_J)+V_D(v*I_J)-P_sh-P_D
      =integral_(F_J)v*(alpha-q_sh-q_D) dW
                                      +Q_D-P_D. (TD11)

Pointwise q_sh<=2/5 and q_D<=(k-2)/5, so the remaining coefficient
is nonnegative throughout the slab. In the K-concentrated region
qK>=1-delta,71 supplies q_sh<=(1+delta)/5, and therefore

    alpha-q_sh-q_D>=(1-delta)/5=:w_D.            (TD12)

The coefficient is the same for linear and quadratic costs. Adding
the actual V5(v*I_J) term and transferring from the complete virtual
deletion V to the actual deletion costs at most vmax*omega, where
omega=(V-actual_deletion)(1)>=0. This uses one positive difference
measure. The old source multiplier and curvature are not applied
again. Equations(TD10)--(TD12) thus bound the same marked credit by

    vmin*w_D*x_J+V5(v*I_J)
                        -C*E_D-vmax*omega-Q*chi,
    Q=sigma_D*C, x_J=W(F_J).                     (TD13)

The original floors and source-increment bounds used here hold for
every46 costs and all independent test layouts, as rechecked from94.

## 4. A single residual gives the uniform interface

Use85's general first-slot packing hypotheses. Let H be the best slot,
r=min_J x_J, m=Lambda(F_H), and G>0 the gap for every other slot.
For its complete cofactor5 family,

    E5>=r/5+G*q5, 0<=q5<=1/5,
    V5(v*I_H)=(1/5-q5)*integral_(F_H)v dLambda
      >=vmin*m/5-(vmin*m/G)*(E5-r/5).            (TD14)

The factor1/5-q5 is nonnegative, so vmin bounds the entire product
before estimating q5. The selected families are disjoint parts of
the original capacity cap. Dropping other nonnegative defects from
91's budget gives

    E_D+(E5-r/5)+omega<=rho-r/5.                 (TD15)

In particular every summand and rho-r/5 are nonnegative. For J=H,
use(TD14) and drop the nonnegative raw-hole contribution. For J!=H,
use x_J>=r+G and discard V5. Both cases of(TD13) are bounded below by

    g-P*(rho-r/5)-Q*chi,
    g=vmin*min(w_D*G,m/5),
    P=max(C,vmin*m/G), Q=sigma_D*C.              (TD16)

Here C>=vmax pays the union error as part of(TD15). Retaining the
old bound gives the positive part in(TD0). The coefficients are
uniform before maximization over each independent original test
layout and averaging with the same actual carrier mixture pi.

For fixed0<=delta<=2/27 and0<=r<=r_star, the slab and packing guards
hold whenever the following common lower bound is positive and the
first three displayed guards are positive:

    h1=1/3-delta/6, eta_min=1/9-delta/18,
    G_star=min(1/10-r_star,
               h1/5-r_star, eta_min/5-r_star,
               h1*(1/10-3*delta/4)-2*r_star)>0.  (TD17)

Using m<=1/9 and m/5>=1/50-r_star/5 gives fixed coefficients

    g_i=vmin_i*min((1-delta)*G_star/5,
                                    1/50-r_star/5),
    P_i=max(C_i,vmin_i/(9*G_star)),
    Q_i=sigma_(D,i)*C_i.                         (TD18)

At delta=1/44 and r_star=1/840, G_star=8/385 and

    g_i=(86/21175)*vmin_i>0,
    P_i=max(C_i,(385/72)*vmin_i).

The actual imbalance has a separate source-escape bound. In71's
product interpolation, every K control has beta supported on root1.
Thus b<=sigma_escape/4, where sigma_escape=1-qK, and

    chi<=b<=sigma_escape/4.                      (TD19)

The deep coefficient sigma_D is different from sigma_escape. The
charge Q_i*chi may be paid against a source-escape reserve. It is
not another copy of the residual rho.

For each cost, the old94 affine gain and(TD0)'s affine gain are
alternatives on the same marked credit. A consumer may use their
maximum with zero, or fixed convex weights whose sum for that cost
is at most1. After taking the original positive comparison weights,
the sum of all selected residual penalties must be charged to the
one common residual coefficient. One may instead minimize the
resulting convex piecewise-affine expression in the same residual.
Adding both full gains or assigning independent residuals is invalid.

## 5. Exact artifacts and boundary

The reusable helper is
[tied_root_deep_payment.py](../../frontier/cover-geometry/tied_root_deep_payment.py).
Its exported function

    uniform_coefficients(cost_rows, delta, rcut)

implements(TD17)--(TD18). It accepts the exact cost rows or serialized
rational rows; rcut is the inclusive actual-r upper bound. It returns
the four guards, G_lower, the common raw-hole coefficient, all46
(g,P,Q) rows, Q/4 escape coefficients, and weighted sums. A separate
consumer must verify its full signed comparison and every outside
branch to assert a global K improvement.

The certificate
[tied_root_deep_payment.json](../../certificates/source_norms/cover-geometry/tied_root_deep_payment.json)
pins94's exact source data and rechecks365 prefix increments and23000
layout/cell floors. It checks the five-ray tied-root cone, all100
independent layout pairs for every46 costs, all complete tail sums,
every original curvature record, and positivity of the default46
g coefficients. The schema is `erdos7-tied-root-deep-payment-v1`.

Regenerate with:

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/tied_root_deep_payment.py --output docs/reports/erdos7-odd-covering/certificates/source_norms/cover-geometry/tied_root_deep_payment.json
```

Verify with:

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/tied_root_deep_payment.py --check
```

On the exact K faces, actual saturation gives E_D=chi=0 and hence
the selected-deep payment is recovered with no remainder. Equations
(TD10)--(TD19) quantify the deviations throughout the stated region;
they do not identify all deep residues with the forced27 carrier,
assume realizability of every relaxed source point, or provide an
arbitrary later-prime continuation theorem.
