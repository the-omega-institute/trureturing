[Index](../../marked_head_profile.md) · [Sharp scalar costs](54-sharp-positive-seven-source-costs.md) · [Threshold optima](58-optimal-original-seven-thresholds.md)

# Unit events force a positive outer-seven compatibility gap

At theta404, independently maximizing all original-seven source blocks
loses a strictly positive amount even after using their sharp individual
norms. For the fixed absorbed carrier(0,1), let Gamma_t be the infimum
of this total loss over independently labelled complete original35
blocks on the same actual source. Then

    7/8575 <= Gamma4 <= 24/8575,
    31/72030 <= Gamma5 <= 39/60025.                    (1)

Here Gamma5 is measured from the sharp positive-block norms of
profile54. Measured from the older envelope, its loss is at least

    831/1200500+31/72030=4043/3601500.                (2)

The result concerns this endpoint and this absorbed carrier. It is
not an exact optimum, a global parameter-domain K improvement, or a
claim of sharp full357 deletion. Profile55's source-only obstruction
still applies. All exponent tails and independent original residues
are retained. The following argument is ordinary mathematics.

## 1. The complete comparison and its loss

Use Lambda, s=1/4, the five cells and ROOT=(0,0,1,1,1) from profile54.
Let A_e>=1 be independently labelled complete original35 test loads.
For each seven count n define

    D_(t,n)(A)=(1/n)*sum_(e<n)h_t(n*A_e)
                         -h_t(sum_(e<n)A_e)>=0.

The probabilities are p1=29/35 and pn=36/(5*7^n), n>=2. The costs
c_(t,e) and absorbed zero cost g_t are those of profiles51 and54,
with omega=(1/5,2/5,0,0,0). Set f0=g_t and f_e=c_(t,e) for e>=1;
write M_e for each sharp source supremum. Explicitly the complete
common-source expression is

    J_t(A)=sum_(e>=0)integral_Lambda f_e(A_e)
                        -sum_(n>=1)pn*integral_Lambda D_(t,n)(A).

Equivalently,

    J_t(A)=integral_Lambda[sum_n pn*(h_t(sum_(e<n)A_e)-h_t(n))
                                      -omega*chi_t(A0)].

Its difference from sum M_e is

    Loss_t=sum_e Delta_e+sum_n pn*integral_Lambda D_(t,n),
    Delta_e=M_e-integral_Lambda f_e(A_e)>=0.          (3)

All sums have complete geometric tails. For n>=t, every A_e>=1
puts both hinge arguments in the affine region, so D_(t,n)=0.
Only n=2,3 for t=4 and n=2,3,4 for t=5 can contribute.

The nested seven-count comparison is valid before this refinement:
it enlarges the original seven-cylinder intersections to their nested
cap intersections as in profile31. The new argument bounds J_t for
arbitrary old-coordinate block loads; it does not assume that the
actual seven cylinders are nested or share residues.

It suffices to use the ten shallow ternary baselines b(r,j). A shallow
test class outside the five surviving cells is zero on Lambda and
can be replaced by a surviving class, increasing the original load
pointwise. The whole expression, before its Jensen decomposition, is
coordinatewise increasing on integer loads: increasing A0 can increase
the subtraction omega*chi_t(A0) only in the step t to t+1; in that
step every full hinge increases by1, giving net increase1-omega>=0.
Positive blocks have no subtraction. Thus this replacement cannot
decrease J_t, and proving the bound after replacement proves it before.

If a block has shallow baseline b, its unit event E={A=1} satisfies

    E subset {cells l with b_l=1}.                  (4)

Later independently chosen mixed labels only increase its load, so
they cannot violate this support inclusion.
Each shallow baseline specifies a unique opposite root containing
its allowed unit support. All root cases below refer to that baseline
root, even if the actual unit event is empty.

## 2. Sharp scalar costs force unit-event mass

For four positive costs the following identities hold at every
integer v>=1, with L(v)=v-1:

    c4,1(v)=(6/35)L(v)-(264/1715)*1_(v>=2),
    c4,2(v)=(6/245)L(v)-(12/1715)*1_(v>=2),
    c5,2(v)=(6/245)L(v)-(177/12005)*1_(v>=2),
    c5,3(v)=(6/1715)L(v)-(9/12005)*1_(v>=2).          (5)

For c=mL-gamma*1_(v>=2), use the universal source bound
integral_Lambda L(A)<=1/2 and Lambda(1)=1/4. Then

    Delta_c+gamma*Lambda(E)
       >=M_c-m/2+gamma/4=gamma*(7/120).

Since Delta_c>=0, for every 0<=alpha<=gamma this implies

    Delta_c+alpha*Lambda(E)>=alpha*(7/120).          (6)

The sharp values M_c in profile54 give the same7/120 in all four
cases. This argument uses neither a common five-adic residue nor a
product representation of arbitrary tests.

## 3. Threshold4

Put I_e=1_(A_e=1). For three positive integer loads,

    D_(4,3)=(I0+I1+I2)/3-I0*I1*I2.                 (7)

The absorbed zero block has unique optimal shallow baseline
b-=(1,1,2,2,3). Any other baseline loses at least1/420, which already
exceeds7/8575. The unit event of b- is confined to root0.

For c4,1 any shallow baseline whose allowed unit support lies in root0 costs
at least69/34300, also exceeding7/8575. Hence any configuration with
smaller total loss must have E0 in root0 and E1 in root1. Their
intersection is empty. Equation(7) therefore yields

    D_(4,3)>=(I1+I2)/3.

Take alpha=p3/3=12/1715. It is at most both coefficients gamma in
the first two rows of(5). Applying(6) separately to A1 and A2 gives

    Delta1+Delta2+p3*integral D_(4,3)
          >=2*(12/1715)*(7/120)=7/8575.             (8)

All unused source deficits and the n=2 Jensen term are nonnegative.
This proves the first lower bound in(1).

## 4. Threshold5

The zero block and sharp c5,1 block both prefer b-. Moving either
baseline costs at least1/735, exceeding31/72030. Thus their unit
events must both lie in root0 in any potentially cheaper case.

If E2 lies in root1, exactly one of A0,A1,A2 is1 on E2. Direct hinge
expansion gives D_(5,3)=2/3 there. With alpha=2*p3/3=24/1715,
which is below gamma5,2=177/12005, equation(6) gives a loss at least

    (24/1715)*(7/120)=1/1225>31/72030.               (9)

Therefore E2 must lie in root0. The exact ten-baseline source bound
shows that its only choice costing less than31/72030 is

    b0=(1,2,2,2,2), with penalty59/144060.           (10)

Every other baseline with units in root0 costs at least151/308700.
For four positive integer loads,

    D_(5,4)=(I0+I1+I2+I3)/4-I0*I1*I2*I3.           (11)

If E3 lies in root1, its fourfold intersection is empty; using
alpha=p4/4=9/12005=gamma5,3 in(6) pays3/68600. Adding(10) exceeds
31/72030. Otherwise E3 lies in root0, which requires source penalty
at least1/48020. In this remaining case the source deficits alone give

    59/144060+1/48020=31/72030.                     (12)

This proves the second lower bound in(1). No assumption of independent
unit events was made; their root supports supplied the needed common
configuration constraint.

## 5. Actual upper witnesses and exact scope

For t=4 take A0=A1=A2=W- from profile54. For t=5 take
A0=A1=A2=A3=W-. Every finite outer Jensen term vanishes. The zero
block is sharp. Direct complete integrals give the positive deficits

    t=4: 69/34300,27/34300, sum=24/8575;
    t=5: 0,127/240100,29/240100, sum=39/60025.

All remaining positive blocks may use W(+,-) and attain their scalar
norms. They occur only in the affine outer region and create no new
Jensen loss. The actual nested seven cylinders[4]_(7^e) approach pn
under the pure7-normalized finite families of profile54. Finite CRT
truncations retain one residue per original modulus, and dominated
convergence gives the upper limits in(1).

The [exact checker](../../frontier/comparison-bounds/finite_outer_jensen_compatibility.py)
and [data](../../certificates/source_norms/comparison-bounds/finite_outer_jensen_compatibility.json)
reconstruct every ten-baseline alternative, the unit-mass constants,
all case-separation inequalities and the explicit upper witnesses:

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/comparison-bounds/finite_outer_jensen_compatibility.py
```

The baseline bounds use the complete two-baseline source theorem of
profile51, with the un-clipped correction and cost-specific affine
slopes of profile54. No finite exponent sampling stands in for the
arbitrary-height proof. The exact Gamma values, the other absorbed
carriers and a global propagation of this correction remain outside
this result. In particular(2) is not an additional credit to costs
already changed by profile53's threshold allocation.
