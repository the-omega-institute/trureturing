[Index](../marked_head_profile.md) · [Generic independent-layout bridge](99-tied-root-deep-payments-use-one-actual-capacity-budget.md) · [One root-imbalance payment](102-one-root-imbalance-charge-reduces-the-deep-capacity-penalty.md)

# Root0 shift thresholds remove the separate imbalance charge

The original root0 baseline order gives more information than the
tied-root comparison alone. A positive marked-shift excess can occur
only in the lower-derivative root0 cell, and that cell must have
strictly smaller availability. The excess vanishes below an explicit
positive imbalance threshold. It can therefore be paid by that
cell's actual unused capacity, with no separate chi remainder.

For adjacent root0 baseline levels m,m+1, put

    v=Delta_m, w=Delta_(m+1), k_h=C-f(m+1),
    tau=(89/180)*v, a=(w-v)/5.

The root0 excess has the upper envelope

    H_m(chi)=min(a,[k_h*chi-tau]_+).              (RT0)

Every original cost has positive convex low increments, so tau>0.
If w=v, the envelope is zero everywhere. Otherwise it vanishes
for chi<=tau/k_h. Its ratio to chi has the exact envelope maximum

    L_m=k_h*a/(tau+a)
       =k_h*(w-v)/(w+(53/36)*v).                 (RT1)

Consequently the complete deep bridge on Delta<=1/18 is

    Q_D-P_D>=-kappa_zero*E_D,
    kappa_zero=max(36*vmax/125,
                   36*(vmax-vmin)/25,L_1,L_2).   (RT2)

This applies to all46 original costs and all independent layouts.
The coefficient is the peak of a proved upper envelope; it is not
claimed to be the least possible coefficient for the actual source.
It trades a potentially larger residual penalty for zero separate
source-imbalance penalty. No global K improvement follows without
checking the shared residual budget again.

## 1. The independent c5 layout retains a root relation

Use99's ten original layouts

    b_l=1+I_ROOT(l)=R+I_l=j, ROOT=(0,0,1,1,1),

including every nonnested R,j pair. Let c5 be an independent member
of the same family. Although c5 is independent of b, its own two
root0 entries satisfy

    |c5_0-c5_1|<=1, c5_l>=1.                    (RT3)

For the cost f and barrier C write

    Delta_a=f(a+1)-f(a), 0<Delta_1<=Delta_2<=Delta_3,
    C>=f(3)+3*Delta_3,
    v_l=Delta_(b_l), k_l=C-f(b_l),
    z_l=k_l*d_l-c5_l*v_l/5, y_l=z_l+v_l/5,
    s_shift=max y-max z.

On the whole slab,99 gives d0,d1>=25/36 and d_j<=5/9 for j>=2.
The root0 baselines are equal or adjacent. If they are equal2,
every other baseline is at most2. If they are equal1, every unsafe
root1 shifted entry is dominated by a root0 baseline1 entry:

    y_root0>=d_root0*(C-f(1))-2*Delta_1/5,
    y_root1<=(5/9)*(C-f(2)),
    y_root0-y_root1
      >=(d_root0-5/9)*(C-f(1))
                       +(5/9-2/5)*Delta_1>=0.   (RT4)

This comparison does not require d0=d1. In both equal-baseline
cases a shifted maximizer has derivative at most the common root0
derivative. Hence neither root0 cell has positive excess.

## 2. Adjacent levels identify the only cell that can incur excess

Suppose the two root0 baselines are m,m+1, with low/high cells L,H.
Then m is1 or2 and the high derivative w=Delta_(m+1) is the maximum
derivative among all five cells. Thus

    s_shift<=w/5,                                (RT5)

so the high cell never incurs positive excess. Every root1 cell
either has derivative at most v=Delta_m or, in the m=1 case, is
dominated in shifted score by the low cell through(RT4).
Therefore a shifted maximizer can be taken to be either the high
root0 cell or a cell with derivative at most v.

In the latter case s_shift<=v/5. In the former, both z_H and z_L
are candidates for the unshifted maximum, giving

    [s_shift-v/5]_+
       <=min((w-v)/5,[y_H-y_L]_+).               (RT6)

Write t=d_H-d_L. Since k_L=k_h+v, one has exactly

    y_H-y_L=k_h*t-d_L*v
                   +((c5_L-1)*v-(c5_H-1)*w)/5.

The original c5 root relation is the additional information:

    (c5_L-1)*v-(c5_H-1)*w
      =(c5_L-c5_H)*v-(c5_H-1)*(w-v)<=v.          (RT7)

Using d_L>=25/36 gives

    y_H-y_L<=k_h*t-(25/36-1/5)*v
            =k_h*t-(89/180)*v.                  (RT8)

If t<=0 the right side is strictly negative, so no excess occurs.
Positive excess requires t>0, when the low-derivative cell is
nonmaximal in availability and t=chi. Combining(RT6)--(RT8) proves
(RT0). In particular, every root0 cell of maximal availability has
zero positive excess, regardless of its baseline.

The coefficient89/180 uses(RT3). Replacing the independent c5 layout
by five unrelated numbers in[1,3] would only give the weaker factor
53/180. No equality or compatibility between b and c5 is assumed.

## 3. Exact envelope peaks give capacity coefficients

For chi>0, the ratio H_m(chi)/chi has three pieces:

    0,                         chi<=tau/k_h;
    k_h-tau/chi,               tau/k_h<=chi<=(tau+a)/k_h;
    a/chi,                     chi>=(tau+a)/k_h. (RT9)

The middle piece increases and the final piece decreases. Their
intersection at chi_peak=(tau+a)/k_h gives(RT1). This remains
valid when a=0, with zero maximum throughout.

If an additional bound0<=chi<=chi_star is available, the exact
maximum of this same envelope ratio on the shorter interval is

    L_m(chi_star)=0,                       chi_star=0;
      [k_h-tau/chi_star]_+,                0<chi_star<=chi_peak;
      k_h*a/(tau+a),                       chi_star>=chi_peak.
                                                    (RT10)

This can be strictly smaller than(RT1), including identically zero
when chi_star does not reach the threshold. No parameter search is
needed to compute either coefficient.

For every selected actual deep label A in cell l, retain102's
two nonnegative capacity pieces

    d_star*3^-a-Lambda(A)
      >=d_star*(3^-a-eta(A))
                      +(d_star-d_l)*eta(A).      (RT11)

Its contribution to P_D-Q_D is still

    u_e*[s_shift*(3^-a-eta(A))
                      +(s_shift-v_l/5)*eta(A)].  (RT12)

The first term is paid with36*vmax/125 times the first piece of
(RT11). On root1, the second term is paid with
36*(vmax-vmin)/25 times the second piece, as in102.

On root0, the only positive second term lies in the lower-derivative
nonmaximal cell. There d_star-d_l=chi. Equations(RT0)--(RT1) give

    (s_shift-v_l/5)*eta(A)
       <=L_m*chi*eta(A)
       =L_m*(d_star-d_l)*eta(A).                 (RT13)

Every label is therefore paid locally from its actual defect. Taking
the maximum of the coefficients for the different nonnegative
pieces and cells proves(RT2). One may replace L_m by(RT10) if its
additional actual-chi bound holds. Empty labels and removed cells
have zero eta and Lambda mass, with their full defect paid by the
first term. There is no residual sum over root0 masses and no
separate sigma_D*C*chi charge.

All actual original labels retain independent residues, and every
e>=1 retains its original u_e=6/(5*7^e). The selected coefficient
is13/1215 for linear costs or8/729 for quadratic costs. The complete
remaining pure3 tails are1/2430 and1/7290, respectively, so the
total deep mass coefficient remains1/90. Absolute convergence is
the same as in99. No deep carrier identification is required.

## 4. Marked source cancellation and the bounded-chi interface

Use the exact source-hole identity99(TD11), with its original source
multiplier and quadratic curvature. Replacing only the deep bridge
gives the same positive source credit and the same single budget

    E_D+(E5-r/5)+omega<=rho-r/5.

The union coefficient is vmax, which dominates the missing-mass
coefficient. Hence, under the original concentration and packing
guards, the fixed uniform interface is

    d_i_actual>=m_i_old+[g_i-P_i*(rho-r/5)]_+,
    g_i=vmin_i*min((1-delta)*G_star/5,
                                    1/50-r_star/5),
    P_i=max(vmax_i,36*(vmax_i-vmin_i)/25,
                        L_(i,1),L_(i,2),vmin_i/(9*G_star)).
                                                    (RT14)

Its separate imbalance coefficient Q is zero. At concentration
sigma_escape<=delta one already has chi<=sigma_escape/4<=delta/4.
Thus(RT10) with chi_star=delta/4 gives a valid smaller uniform P
under exactly the same concentration assumptions. It consumes no
additional source-escape reserve.

This changes the distribution of losses between the residual and
source escape. P can exceed102's P even though Q is zero, and a
sum of these penalties can exceed the available common residual
coefficient. A global consumer must choose valid alternatives or
convex combinations per original cost and check the full budget.
The old and new marked gains cannot be added for the same cost.

## 5. Exact artifacts and scope

[root0_shift_threshold.py](../frontier/root0_shift_threshold.py)
exports the exact one-case envelope through `root0_case` and the
all-cost interface through

    uniform_coefficients(cost_rows, delta, rcut,
                         use_concentration_bound=True).

The default uses chi<=delta/4. Setting the last parameter to false
uses the unbounded envelope peak. A direct `root0_case` call with
`chi_upper` requires that additional bound on the actual imbalance.
The original actual-r cutoff remains inclusive.

The [certificate](../certificates/source_norms/root0_shift_threshold.json)
has schema `erdos7-root0-shift-threshold-v1`. It revalidates102's
source data,365 prefix increments,23000 floors and complete tails;
checks all100 original independent layout pairs and4600 cost/layout
adaptations; and verifies the exact onset, peak and coefficient
identities for both adjacent-level cases of every cost. It retains
the bounded and unbounded coefficient vectors at103's fixed source
parameters. These finite checks supplement the general proof of
(RT9)--(RT13); they do not enumerate an infinite source family.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/root0_shift_threshold.py --output docs/reports/erdos7-odd-covering/certificates/source_norms/root0_shift_threshold.json
python3 -I -O docs/reports/erdos7-odd-covering/frontier/root0_shift_threshold.py --check
```

The result is an ordinary theorem and reusable exact interface.
It asserts neither a new global K nor optimality of the upper
envelope for actual sources. Lean verification, unrestricted
Erdos #7 and arbitrary later-prime continuation remain open.
