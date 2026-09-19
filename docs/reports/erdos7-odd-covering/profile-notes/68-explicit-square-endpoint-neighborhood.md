[Index](../marked_head_profile.md) · [Complete endpoint square](64-one-zero-seven-layout-and-complete-pure-three-tails.md) · [Quantitative source geometry](66-explicit-linear-endpoint-neighborhood.md) · [Whole numerator](65-endpoint-numerator-from-common-cost-constraints.md)

# An explicit neighborhood for the square bound469/100

Keep exactly the actual measures, effective9 source branch, cell labels,
source deviations tau, mass slack epsilon=S-D, and carrier deviation
kappa=1-pi_(root0,cell1) from profile66. In particular

    tau=||eta-eta*||_1+||n-n*||_1+||d-d*||_1+delta_s+delta_L,
    delta_s=(z-3/4)+(1/4-alpha1)+(1/4-beta2),
    delta_L=1/72-late3,

and (eta*,n*,d*) is source vertex404. Assume

    tau<=1/1000, epsilon<=1/10000.                 (Q1)

Then every independently labelled original357 test A, with unit1,
satisfies the explicit bound

    integral_survivor A^2<=469/100+Phi(tau,epsilon,kappa),
    Phi=1650*tau+17400*epsilon+101*kappa+41*sqrt(epsilon). (Q2)

All original test labels may have independent residues, and all exponent
tails remain included. In particular Phi tends to0 with the three
deviations. An exact min-geometric variant is given below and may be
used instead of the square-root terms by a quantitative consumer.

The actual signed margin is at least

    45*S-469/100-Phi.                             (Q3)

This retains the same actual S in every cost inequality. If a scalar
lower bound is desired, (Q3) is at least

    103/50-Phi-72*tau+45*epsilon.

No replacement of a signed mass term by an upper mass bound is used.

On the nonzero box

    tau<=1/1000000, epsilon<=1/1000000000000,
    kappa<=1/1000000,                             (Q4)

the new square bound improves the inherited uniform square estimate
G*S, G=102715/2916, by more than1/2. This comparison is with that
specified inherited uniform norm, not a claim about all possible
stronger square comparisons. The complete global K consumer and
the physical denominator remain separate obligations.

This is an ordinary mathematical proof, not Lean verification.

## 1. Quantitative source geometry supplied by profile66

Write the five first-five slots as P,A,Beta,Q,H. Profile66 proves
the presence and distinctness needed to use those slots on (Q1).
Let ell=h/5-Lambda(H). The bounds needed here are

    ell<=35*epsilon/6, eta2>=1/10, h1-h0>=1/9,
    beta_err=2*delta_s+ell/eta2<=2*tau+60*epsilon. (Q5)

Let c_lj be the pre-late endpoint coefficients of profile64, i.e.
the source-slot table divided by eta_l. Before late deletion, the
actual source on an arbitrary pure3 cylinder J in cell l obeys

    Lambda(J times slot j)
      <=eta(J)*(c_lj+beta_err*1_(j=Q)).           (Q6)

This is the assigned-shallow-budget argument in profile66. It holds
on every J because pure5, root1-alpha and cell2-beta exclusions have
the same five-coordinate sections throughout their ternary support.
Dropping additional late deletion only increases the upper bound.

For the full cell-slot matrix, retaining late deletion as in66(N8)
gives some x' in[1/90,1/72] such that

    sum_(l,j)(Lambda_lj-M_lj(x'))_+
      <=14*tau+76*epsilon.                       (Q7)

Here M is the exact endpoint source matrix. Let

    w_lj=1-(1_root0+1_(l=1)+1_(j=H)
                                   +1_(root1 and j=H))/5,
    k_lj=w_lj*c_lj.

The four selected forbidden cofactor families3,9,5,15 give an
actual positive error measure nu with

    mu<=w*Lambda+nu,
    nu(1)<=201*epsilon+2*kappa/5.                (Q8)

This is stronger than just applying66(N6) separately to each cell.
Indeed nu is the positive sum of V-delta, the missing correct
cofactor3/cofactor9 carrier weights times the corresponding source
restrictions, and the two bad cofactor5/cofactor15 weight bounds
times their H restrictions. Their total weights are exactly those
used in66(N6), so one total error pays a whole partition at once.

Let u_lj be profile63's endpoint entry capacities, and r_l its five
endpoint row capacities. By (Q7)--(Q8), actual surviving cell-slot
masses t_lj satisfy

    sum_(l,j)(t_lj-u_lj)_+<=14*tau+277*epsilon+2*kappa/5.

The five individual row bounds obtained from66(N10) imply

    sum_l(sum_j t_lj-r_l)_+<=10*tau+20*epsilon+2*kappa.

Finally the excess of actual total mass over3/20 is at most
8*tau/5+epsilon. These are three distinct capacity-error bounds;
adding them is conservative even when some of their supports overlap.

## 2. The bounded shallow square and its raw source norm

For a fixed six-label layout B, 1<=B_lj<=6. Its nonconstant square
coefficients B_lj^2-1 lie between0 and35. Every dual certificate used
in profile63 has nonnegative entry, row and total multipliers at most35.
This also follows from its displayed construction: gamma is a load
coefficient, beta is a nonnegative difference from gamma, and alpha
is the remaining nonnegative coefficient. The checker verifies these
bounds for all12500 layouts.

Applying the same feasible dual to the actual capacities and the
three positive-excess bounds above gives, for that same B,

    integral_mu(B^2-1)<=Z6(B)+z_head,
    z_head=896*tau+10430*epsilon+84*kappa.        (Q9)

No actual mass table is asserted feasible for the endpoint LP.
The extra dual payment in (Q9) explicitly accounts for all violations.

Since B^2<=36, (Q7) gives the raw source bound

    integral_Lambda B^2<=R6(B)+36*(14*tau+76*epsilon), (Q10)

where R6(B) is the maximum of its two endpoint raw-source values.
The same layout B occurs in (Q9) and (Q10).

## 3. Weighted deletion on an arbitrary deep cylinder

Let J be any original pure3 test cylinder of depth a>=3, lying in
cell l. For its shallow layout put

    w_a(l,j)=2*B_lj+2a-5,
    0<=w_a(l,j)<=W_a=2a+7.

As in64, the four selected forbidden families and the additional
families5^b and3*5^b with b>=2 are distinct original labels.
We retain both groups.

For the additional families, call an old-coordinate label good
when its five cylinder lies in Q or H, and, for3*5^b, its ternary
root is1. A good label's product-to-source loss on J is at most its
global old-coordinate cap deficiency. A label in P,A,Beta loses at
least eta2*5^-b from that cap; a wrong root loses at least
(h1-h0)*5^-b. Missing labels lose their whole cap. On (Q1) these
losses pay at least one tenth of the desired product mass on J.
For any slot weight between0 and W_a, each bad label's missing
weighted contribution is therefore at most10*W_a times its cap
deficiency.

After summing all b>=2 and e>=1, these families supply at least

    eta(J)*ell_l*min(w_a(l,Q),w_a(l,H))-10*W_a*epsilon,
    ell_l=(1+1_root1)/100.                       (Q11)

For the3*5^b family the desired contribution is zero if J lies in
root0. Thus (Q11) never relocates a wrong-root label to a new root.
It compares the desired quantity and the actual quantity through
the original label's own unused cap. The two complete sums are
sum_(b>=2)5^-b=1/20 and sum_e u_e=1/5.

The bad weight of each of the two first-five forbidden families is
at most100*epsilon. Its weighted source integral on J is at most
W_a*eta(J); the two shallow ternary carrier errors cost at most
(2*kappa/5)*W_a*eta(J). The final V-to-delta transfer costs at most
W_a*epsilon. Using (Q6), (Q11), and eta(J)<=3^-a gives

    integral_J w_a dmu
      <=3^-a*z_l(a)+W_a*[g*3^-a+11*epsilon],
    g=2*tau+260*epsilon+2*kappa/5.                (Q12)

Here z_l(a) is exactly profile64's nonnegative affine expression

    z_l(a)=sum_j k_lj*w_a(l,j)
                        -ell_l*min(w_a(l,Q),w_a(l,H)).

Its nonnegativity follows from k_lQ+k_lH>=ell_l, as in64. The
errors added before replacing eta(J) by3^-a are nonnegative too.

A second bound is integral_J w_a dmu<=W_a*3^-a, using domination
by the full pure3-times-pure5 product measure. Combining it with
(Q12), and using z_l(a)>=0, yields

    integral_J w_a dmu
      <=3^-a*z_l(a)+W_a*g*3^-a
                         +W_a*min(11*epsilon,3^-a).       (Q13)

This minimum is essential. Summing W_a*epsilon without the second
cap would diverge, and no such summation is used here.

## 4. Complete expanded-head errors

For every independently chosen pure3 test sequence,

    X=B+sum_(a>=3)1_(J_a),
    X^2-B^2<=sum_(a>=3)w_a*1_(J_a).

The same pointwise inequality and complete affine tails from64
apply. Since sum_(a>=3)(2a+7)*3^-a=7/9, (Q13) gives

    integral_mu(X^2-1)<=Z(B)+z,
    z=900*tau+10700*epsilon+85*kappa+T(epsilon),
    T(epsilon)=sum_(a>=3)(2a+7)*min(11*epsilon,3^-a). (Q14)

For raw source tails, (Q6) gives an error at most
(7/9)*beta_err. Together with (Q10), this yields

    integral_Lambda X^2<=R(B)+r,
    r=510*tau+2800*epsilon.                      (Q15)

The functions Z(B),R(B) are exactly those of64, with all pure3
depths included. We have not truncated the head or multiplied a
total-variation error by an unbounded complete load.

The function T is explicitly computable: for positive epsilon,
find the first integer n>=3 with3^-n<=11*epsilon, use the finite
constant segment up to n, and the complete weighted geometric tail
thereafter. At epsilon=0 put T(0)=0. In particular

    T(epsilon)<=35*sqrt(epsilon).                (Q16)

One elementary proof uses min(x,y)<=sqrt(x*y),
1/sqrt(3)<3/5 and sqrt(11)<4. Then the coefficient of sqrt(epsilon)
is at most4*sum_(a>=3)(2a+7)*(3/5)^a=864/25<35.

## 5. The common zero-seven layout survives perturbation

Profile64 has Rstar=212153/87480<5/2 and
1/4<=R(B)<=Rstar for every layout. The lower bound follows already
from B^2>=1 and the endpoint raw source mass1/4.

For any such R(B), Rstar and any r>=0,

    sqrt((R(B)+r)*(Rstar+r))<=sqrt(R(B)*Rstar)+2*r. (Q17)

Indeed if x=Rstar/R(B), then1<=x<=10 and
(x+1)^2<=16*x: x^2<=10*x gives x^2-14*x+1<=-4*x+1<=0.
Thus R(B)+Rstar<=4*sqrt(R(B)*Rstar); squaring the nonnegative
two sides in (Q17) finishes the proof.

Keep the zero-seven block's own B in its surviving and raw bounds.
Positive-depth blocks can have entirely independent layouts and
test residues. The pairwise seven cap and Cauchy-Schwarz argument
of64 gives an error in the replaced expanded-head pair sum at most

    z+(2/5)*(2*r)+(4/15)*r=z+(16/15)*r.         (Q18)

The factors2/5 and4/15 include all seven depths exactly. No common
seven residue at one depth is assumed, and the pure7 test labels
remain the old-unit terms in their respective blocks.

## 6. The unreplaced pairs also have an explicit complete error

Every ordered pair outside the expanded head retains its old62
endpoint cylinder cap plus the corresponding positive error from66.
The total error for this subset is at most the error for the whole
complete pair-cap table, because all its error terms are nonnegative.
This enlargement overcounts some errors but does not deduct any
head contribution twice.

The zero-seven error contributions are

    unit:          8*tau/5+epsilon,
    modulus3:      3*(2*tau+4*epsilon+2*kappa/5),
    modulus9:      5*(2*tau+4*epsilon+2*kappa/5),
    modulus5:      3*(14*tau+300*epsilon+kappa),
    modulus15:     9*(14*tau+300*epsilon+kappa),
    pure3 a>=3:    (4/9)*(tau+2*kappa/5)+T3(epsilon),
    pure5 b>=2:    (11/40)*(tau+2*kappa/5)+T5(epsilon),
    3*5^b,b>=2:    (33/40)*tau,
    9*5^b,b>=1:    (35/8)*tau,
    deep35:        0,

where

    T3(epsilon)=sum_(a>=3)(2a+1)*min(4*epsilon,(1/5)*3^-a),
    T5(epsilon)=sum_(b>=2)(2b+1)*min(epsilon,(1/18)*5^-b).

The entire raw35 pair-cap table changes by at most(1247/72)*tau.
Its complete positive-seven multiplier is2/3. Therefore the total
unreplaced-pair error is at most

    E_err=204*tau+3633*epsilon+16*kappa+T3(epsilon)+T5(epsilon). (Q19)

Again T3 and T5 are exact finite constant segments plus complete
weighted geometric tails. They satisfy

    T3(epsilon)<=5*sqrt(epsilon),
    T5(epsilon)<=sqrt(epsilon).                 (Q20)

For T3, use sqrt(4/5)<1 and1/sqrt3<29/50; then
sum_(a>=3)(2a+1)*(29/50)^a<5. For T5, use1/sqrt18<1/4 and
1/sqrt5<1/2, giving a coefficient at most
(1/4)*sum_(b>=2)(2b+1)*2^-b=7/8<1.

## 7. Combine the unchanged endpoint comparison and the errors

The endpoint head/remainder decomposition of64 is a disjoint
decomposition of ordered original-label pairs. Its endpoint total
is at most469/100, by the12500 rational common-layout comparisons.
The same decomposition near the endpoint is bounded by that total
plus (Q18) and (Q19). Thus a slightly sharper explicit error than
(Q2) is

    1648*tau+(51959/3)*epsilon+101*kappa
                            +T(epsilon)+T3(epsilon)+T5(epsilon). (Q21)

Using (Q16),(Q20), and rounding the two rational coefficients up
gives (Q2). Both (Q2) and (Q21) are uniform over arbitrary independent
original labels; the polynomial-geometric bounds justify every
infinite passage by nonnegative convergence.

Finally S>=3/20-8*tau/5+epsilon gives

    G*S-[469/100+Phi]
      >=[G*(3/20)-469/100]-(8*G/5)*tau-Phi.

At the corner of (Q4) the right side is strictly greater than1/2;
the exact checker verifies this rational comparison with
sqrt(epsilon)<=1/1000000. The actual finite construction of50
eventually enters (Q4), and its closed parameter formulas give an
explicit finite-height witness in the certificate.

This local numerator inequality is available for later use in65's
signed-cost comparison. Its positive numerator progress alone does
not settle a uniform denominator or the rest of the source domain.

## 8. Exact checks and scope

The [checker](../frontier/endpoint_square_neighborhood.py) reconstructs
the [certificate](../certificates/source_norms/endpoint_square_neighborhood.json)
with `python3 -I -O .../endpoint_square_neighborhood.py --check`. It
rechecks12500 inherited feasible primal/dual equalities and bounds
every dual multiplier by35; it also checks the complete error
inventory, the rational square-root estimates, independent full
weighted-tail evaluations, and the strict box comparison.

The closed construction formulas of50 place the height24 actual
finite family inside (Q4), with15624 distinct nonunit original labels.
The program evaluates those proved formulas; it does not enumerate
the height24 CRT period. The finite computations certify the stated
constants and LP bounds. The arbitrary-label measure comparisons
and uniform unbounded-tail argument are the ordinary proof above.
