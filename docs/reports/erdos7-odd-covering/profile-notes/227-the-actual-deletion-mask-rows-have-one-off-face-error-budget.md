[Index](../marked_head_profile.md) · [Actual deletion masks](222-deep-five-deletion-retains-the-selected-observation-masks.md) · [One packing budget](117-the-actual-slot-defects-share-a-stronger-packing-polytope.md) · [Complete family defects](125-the-complete-off-face-omitted-tails-recover-every-face-constant.md) · [Established source domains](208-the-expanded-seven-survival-bound-covers-both-wide-source-domains.md)

# The actual deletion-mask rows have one off-face error budget

Five groups in222's E5 interface have explicit error bounds away
from saturation: the five inherited E5 row totals, eight marked
ternary marginals, five fixed-H raw marginals, fifteen support-zero
rows and four hundred common-mask inequalities. The25 mask
aggregation equalities remain exact. All errors use the same actual
source, actual virtual deletion and residual budget.

This is a partial transport interface. It does not transport every
constraint in216/223, the retained135/125 caps, every pruning
candidate or the complete objective and tail. Consequently no new
off-face or global K bound follows from this interface alone.

## 1. Actual families and their complete product references

Use117/125's canonical K orientation and195/208's established
source-domain guards. Write eta for the actual ternary source,
h0,h1 for its two root masses, h=h0+h1, and etaL for its first-beta
cell mass. Thus h1>h0 and etaL>0. Keep the original source Lambda,
actual survivor mu and projected virtual and actual deletions V,delta:

    W=V-delta>=0, omega=W(1), mu=Lambda-V+W.

Let Vp and Va be the complete virtual forbidden families5^b*7^e
and3*5^b*7^e, respectively, with b>=2,e>=1. Their existing defects are

    Ep=h/100-Vp(1)>=0,
    Ea=h1/100-Va(1)>=0.                              (MT1)

These are125's E5d,E15d. They have disjoint original labels from
the shallow5/15 families. Therefore117's packing inequality gives

    (r+r1)/5+Ep+Ea+omega+G*(q5+q15)<=rho,             (MT2)

after discarding the other nonnegative distinct family defects.
Here G>0 is a valid common gap on the stated source neighborhood;
r is the actual best-slot loss and0<=r1<=r. There is one rho.

For each present pure-five label choose its actual five cylinder;
for an absent label choose any cylinder of the same depth as a
reference only. With u_e=6/(5*7^e), form the positive five measure

    nu_p=sum_(b>=2,e>=1)u_e*Haar5|J_(b,e),
    nu_p(1)=(1/5)*sum_(b>=2)5^-b=1/100.

Since Lambda<=eta tensor Haar5 label by label,

    Pp=eta tensor nu_p,
    Pp-Vp>=0, (Pp-Vp)(1)=Ep.                         (MT3)

For the alpha-five family separate its present root1 and wrong-root
parts as Va=Vgood+Vwrong. Removed roots contribute zero actual mass.
Use each root1 label's actual five cylinder, and any same-depth
cylinder for each wrong-root or absent reference. The resulting
nu_a has mass1/100, and

    Pa=eta|root1 tensor nu_a,
    Pa-Vgood>=0, (Pa-Vgood)(1)=Ea+Vwrong(1).

A wrong-root label has actual mass at most u_e*h0*5^-b and nominal
deficit at least u_e*(h1-h0)*5^-b. Consequently, putting
kappa=h1/(h1-h0),

    Vwrong(1)<=(kappa-1)*Ea,
    ||Pa-Va||_TV=Ea+2*Vwrong(1)<=(2*kappa-1)*Ea.       (MT4)

The norm here is total signed-measure variation, without a factor
one half. The equality follows because Pa-Vgood and Vwrong live on
different roots. Every sum is a complete positive geometric sum;
monotone convergence includes arbitrary heights and absent labels.

For the actual virtual deep-five deletion z=Vp+Va and P=Pp+Pa,

    ||z-P||_TV<=B, B=Ep+(2*kappa-1)*Ea.               (MT5)

Neither nu_p nor nu_a is asserted to have Q/H support off the face.
The actual z is retained; the references do not relabel its events.

## 2. Cell totals, marked marginals and the fixed best slot

Let eta*=(1/18,1/9,1/9,1/9,1/9) denote only the five face cell
masses. Source concentration gives

    sum_c|eta_c-eta*_c|<=sigma/9,
    sum_(c>=2)|eta_c-eta*_c|<=sigma/18.               (MT6)

These are finite-vector bounds. No fixed reference measure inside
the thinned cell0 is required. On cells1 through4, eta is dominated
by ternary Haar, and their total missing Haar mass is at most
sigma/18.

Let e_c=z(cell_c times X5). Product P has row totals
eta_c*(1+ROOT(c))/100. Applying(MT5) to the cell partition and then
(MT6) yields

    sum_c|e_c-eta*_c*(1+ROOT(c))/100|
       <=B+sigma/600.                               (MT7)

For the independent original27 and81 tests keep their actual
membership masks. A present test of positive source mass uses its
own parent-cell point projection lambda27 or lambda81. In cells1
through4, their Haar masses are eta*_c/3 and eta*_c/9. Under P,
their masses are instead eta(J)*(1+ROOT(c))/100. The total error
from missing Haar is at most sigma/900 for each of the two tests.
Restricting z-P to each test adds at most B. Thus the eight signed
residuals of222(DM8) satisfy

    sum_(eight rows)|marked_residual|<=2*B+sigma/450. (MT8)

Absent or source-null tests are a separate case: their raw,
surviving and z-marked masses are zero, and their dummy projection
is placed in cell0. All unthinned marked rows are then exactly
zero. No Haar reference at their original parent is used in this
case. This is the existing222 embedding convention, not a claim
that arbitrary convex projection mixtures are actual residues.

For the actual best five slot H, domination gives five nonnegative
deficits eta_c/5-Lambda(cell_c,H), whose sum is r. Hence

    sum_c|Lambda(cell_c,H)-eta*_c/5|<=r+sigma/45.     (MT9)

The25 equalities summing the z masks to their coarse e5 cells are
identities of actual measures and have zero error everywhere.

## 3. Forbidden first slots pay their own family deficits

The established guards force source slots P,A,B with the same
exclusions as117: P is removed everywhere, A on root1, and B in
cell L. Each depth-b five cylinder lies in one first slot.

For a pure-five label in A, actual mass is at most h0 times its
weighted five length while its deficit is at least h1 times that
length. In B the corresponding factors are h-etaL and etaL. Its
mass in P is zero. Therefore the complete pure-family mass in the
three forbidden slots is at most beta_p*Ep, where

    beta_p=max(h0/h1,(h-etaL)/etaL).

A root1 alpha-five label has zero mass in P/A; in B the ratio of
actual mass to deficit is at most(h1-etaL)/etaL. Every wrong-root
label has ratio at most h0/(h1-h0), irrespective of its slot.
Consequently

    z(P union A union B)<=beta_p*Ep+beta_a*Ea,
    beta_a=max((h1-etaL)/etaL,h0/(h1-h0)).            (MT10)

The cases partition original labels before the maximum is taken.
Absent labels have zero actual mass. Thus each family deficit is
used once, including its entire exponent tail.

## 4. One actual overlap measure pays all common-mask rows

Write C_i for the original cell/slot/mask atoms, x_i=Lambda(C_i),
y_i=mu(C_i), z_i=z(C_i). Removing just the four shallow families
3,9,5,15 from V leaves both z and all other virtual families
nonnegative. The established208 shallow upper density is

    wbar(c,s)=wface(c,s)+(d/5)*I_(c!=0)
                 +q5*I_(s=H)+q15*I_(c>=2,s=H),       (MT11)

on sigma<=d. It follows from mu=Lambda-V+W that

    y_i+z_i-wface_i*x_i
       <=(wbar_i-wface_i)*x_i+W(C_i).                (MT12)

All400 atoms partition the same source. For nonnegative row prices
u_i, their overlap charge is at most(max_i u_i)*omega, not one
omega per atom. If the coarse E3+E5 inequalities are also priced,
their additional prices must be combined on this same W before
using its budget.

## 5. Signed dual prices give an explicit shared error bound

For these five groups of face constraints, let

    T=max absolute price of the five E5 total equalities,
    M=max absolute price of the eight marked equalities,
    Hprice=max absolute price of the five fixed-H equalities,
    S=max nonnegative price of the fifteen support-zero rows,
    u_(c,s)=max_mask u_(c,s,mask), Q=max_(c,s)u_(c,s).

Negative equality prices are included through absolute values.
Take cbar_(c,s) to be208's uniform capacities for this same actual
raw source, and bound kappa,beta_p,beta_a uniformly on the domain.
The following explicit choices follow from source concentration:

    kbar=(6-d)/(3-2*d),
    hbar=1/2+d/18, h0bar=1/6+d/18,
    h1min=1/3-d/18, etaLmin=1/9-d/18,
    bp=max(h0bar/h1min,hbar/etaLmin-1),
    ba=max((1/3)/etaLmin-1,kbar-1).                  (MT13)

Here h1<=1/3 follows from Haar domination. Set

    L=max(5*Hprice,
          T+2*M+bp*S,
          (2*kbar-1)*(T+2*M)+ba*S,
          Q),
    C=T/600+M/450+Hprice/45
                       +(1/5)*sum_(c!=0,s)cbar_(c,s)*u_(c,s),
    B5=sum_c cbar_(c,H)*u_(c,H),
    B15=sum_(c>=2)cbar_(c,H)*u_(c,H).                (MT14)

Then the total priced residual of these433 face constraints is
bounded by

    d*C+q5*B5+q15*B15+[rho-G*(q5+q15)]*L
       <=d*C+rho*max(L,B5/G,B15/G).                 (MT15)

To prove the first inequality, combine(MT7)--(MT12) before spending
the residual. Their primitive prices are respectively5*Hprice on
r/5, T+2*M+bp*S on Ep, (2*kbar-1)*(T+2*M)+ba*S on Ea, and Q on
omega. Equation(MT2) bounds their common total. For the second
inequality the three nonnegative weights

    G*q5, G*q15, rho-G*(q5+q15)

sum to rho. This is an affine budget identity; it does not require
convexity of a parameter-dependent LP optimum.

When the other LP constraints are transported, their prices must
first be added to the same primitive defect prices. Independently
maximizing each group and calling all of them the same rho would
discard the coupling and cannot establish a tighter shared bound.

## 6. Signed equality prices preserve the common defect measures

A sharper bound keeps the signs before taking any supremum. Let
t_c,b_c,g_c,h_c be the five total, four27, four81 and five fixed-H
equality prices, with b_0=g_0=0. On the ternary coordinate define

    phi=t_c+b_c*I27+g_c*I81,
    A5=sup(-phi)_+,
    A15=sup_root1(-phi)_+,
    B15=sup_root0(phi)_+.

For a source-null or absent test its effective event in phi is the
empty set. Its actual marked masses are zero and its dummy cell0
projection makes every unthinned target zero. Using a nonempty
Haar cylinder at its original parent would not give the same
equality residual. For positive events use the actual cylinders.
All suprema can safely use all four membership-bit pairs on each
cell, containing both nested and disjoint alternatives.

The positive measures Pp-Vp and Pa-Vgood have masses Ep and
Ea+Vwrong(1); the second is supported on root1. The wrong-root
measure is supported on root0. Consequently

    integral phi d(z-P)
       <=A5*Ep+[A15+(kbar-1)*(A15+B15)]*Ea.           (MT16)

Let S now maximize only the A/B support prices; z(P)=0 exactly.
The resulting two deep-family prices are

    p5=A5+bp*S,
    p15=A15+(kbar-1)*(A15+B15)+ba*S.                (MT17)

For the source perturbation put a=eta0-1/18 and let Sigma be the
positive missing Haar measure on cells1 through4. Concentration
gives0<=Sigma(1)<=a<=sigma/18. Write gamma_c=(1+ROOT(c))/100 and

    C0=t_0/100+h_0/5,
    CU=sup_(c!=0)[-gamma_c*phi-h_c/5].

The combined total/marked/H source perturbation is exactly
a*C0+integral[-gamma_c*phi-h_c/5]dSigma, hence is at most

    sigma*Csign,
    Csign=(1/18)*max(0,C0+max(0,CU)).                (MT18)

This prices one source deficit measure. In particular a positive
equality price on a row whose perturbation is negative need not
be converted into a positive charge.

For the remaining H-slot loss let

    L0=max_(c<2)(-h_c)_+,
    L1=max_(c>=2)(-h_c)_+.

The actual losses ell_c=eta_c/5-Lambda(c,H) sum to r, and their
root1 subtotal is r1. The original shifted shallow coordinates
Y1=E5-G*q5 and Y2=E15-G*q15 satisfy Y1>=r/5,Y2>=r1/5. Thus

    -sum_c h_c*ell_c
       <=5*L0*Y1+5*(L1-L0)_+*Y2.                   (MT19)

Together with the deep-family and union coordinates, the same
seven-coordinate residual simplex from208 has largest added price

    Lsign=max(5*L0,5*(L1-L0)_+,p5,p15,Q).            (MT20)

The virtual z is used throughout, so its row totals require no
additional union-deletion error. The union price Q pays(MT12).

Finally retain208's fixed25-node raw polytope with both its uniform
capacities and three group budgets. Put

    Hu(q)=max_X sum_(c,s)u_(c,s)*
          [(d/5)*I_(c!=0)+q5*I_H+q15*I_(root1,H)]*X_(c,s).

It contains the actual raw vector. Its feasible set is independent
of q and its objective is affine in q, so Hu is convex. A uniform
signed bound for the same433 rows is therefore

    d*Csign+max_(q in vertices)
                [Hu(q)+(rho-G*(q5+q15))*Lsign],       (MT21)

where the vertices are(0,0),(rho/G,0),(0,rho/G). Every raw LP has
an exact primal/dual equality. This convexity argument concerns
the fixed raw polytope only; it does not assert convexity of a
retained LP whose constraints themselves contain q. The minimum
of the complete uniform bounds(MT15) and(MT21) is also valid.

## 7. Exact price consumer and remaining obligations

The [helper](../frontier/selected_deletion_mask_row_transport.py)
checks the physical meanings of all433 priced rows and25 exact
aggregation rows in both223 branches. It reconstructs195/208's two
established source domains and their25 uniform capacities, then
evaluates(MT13)--(MT21) on all2060 already certified223 duals. The
[certificate](../certificates/source_norms/selected_deletion_mask_row_transport.json)
stores the exact maxima and both heavy controllers' component
prices, including signed source prices and the raw LP primal/dual
witnesses. It reads split inputs through the existing certificate IO.

| Source domain | Maximum coarse row-error bound | Maximum after signed transport |
| --- | ---: | ---: |
| sigma<=1/20, rho<=1/1000 | 2.6955264379839434 | 0.5164472081648043 |
| sigma<=1/12, rho<=1/3000 | 0.9948426286434120 | 0.2562409485739219 |

Each maximum ranges over all2060 stored duals, with the minimum of
the two whole-domain bounds taken for each dual before its final
maximum. These are prices for the five constraint groups, not
changes to the complete K comparison.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/selected_deletion_mask_row_transport.py --check
```

These computed numbers price only the stated row residuals. They
are not added to a face objective and reported as a complete
off-face bound. The inherited raw and survivor constraints, pure3
deletion rows, retained-label rows, full omitted tails, objective
changes and complete scan alternatives still require compatible
transport. No new K value or Lean/frozen result is asserted.
