# Seventeen prescribed old projections control the actual thirteen-row loss

Throughout, the complete original family is finite and supported on
`Q={5,7,11,13,17,19}`. Every full numerical modulus has at most two
originals, including rows17 and19.

Let `H5,H7 >= 4` be independent finite integers. Use the old original family

- for `p = 5,7` and `1 <= e <= Hp`, the residues `p^(e-1)` and `2 p^(e-1)` modulo `p^e`;
- for `1 <= a <= H5`, `1 <= b <= H7`, the two CRT pairs `(3*5^(a-1), 3*7^(b-1))` and `(3*5^(a-1), 4*7^(b-1))` at the full label `5^a 7^b`.

Retain exactly [Report558](558-first-eleven-inventory-and-an-actual-phase-counterexample.md#3-a-fully-fixed-finite-counterexample-with-both-root11-copies)'s literal 25-row, two-slot first11 table at current11 exponents `1,...,4`. This gives 200 first11 originals. All phases are fixed globally.

Write

\[
D=\{5^a7^b11^c:0\le a,b,c\le4\}.
\]

For each `d` in this 125-label set let `r_d` be [Report558 Section4](558-first-eleven-inventory-and-an-actual-phase-counterexample.md#4-the-finite-query-and-exact-first11-response)'s fixed query phase, including the unit. Impose that old-projection restriction only at the following 17 old cofactors:

\[
D_{17}=\{5,7,11,25,35,49,55,77,121,125,175,245,275,343,385,539,605\}.
\]

The row13 originals may have any finite collection of old cofactors supported on `5,7,11`, at any finite current13 heights, with at most two originals per full numerical label. If the old cofactor lies in `D17`, each original must have old projection `r_d`. All other old projections, every current13 phase, and all later17/19 originals are arbitrary. Every phase is fixed globally. Use one actual PA source in the order `5,7,11,13,17,19`, with no intermediate normalization. The prescribed old-comb family and the exact first11 table above remain part of the hypotheses.

Use the actual capped conditional kernels from
[Report348](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md#retaining-the-actual-pure-anchor-masses).
Their density caps at primes11,13,17,19 are respectively5/3,3/2,2,9/5.
For the final supported probability `nu`, write

\[
R_Q(\nu)=\sum_{\substack{d>1\\p\mid d\Rightarrow p\in Q}}
\max_{a\bmod d}\nu(a\bmod d).
\]

The sum includes every query height, independently of actual original heights.
Then this class admits a same-law complete-query bound

\[
R_Q\le
\frac{728860641071559460125956988937}
     {144709874209547238079280572416}
=5.036702886052767\ldots<\frac{257}{51},
\qquad Q=\{5,7,11,13,17,19\}.
\]

This is an ordinary proof with exact rational computations, not a Lean verification or an unrestricted NC4 result.

## Actual union loss clips the query overload

On an actual pre13 history `x`, let

\[
L(x)=\sum_{d\in D}\mathbf1_{\{x=r_d\pmod d\}}.
\]

First retain only the actual13 originals whose old cofactors lie in `D17` or are the unit, and call their forbidden Haar fraction `b0(x)`. For every current exponent, each matching old query supplies at most two retained actual13 congruences. Since the retained cofactor set is a subset of `D`,

\[
b_0(x)\le\min\left(1,2L(x)\sum_{e\ge1}13^{-e}\right)
=\min(1,L(x)/6).
\]

With the PA cap `C13=3/2`, the retained-family fibre loss on this same actual pre13 source is

\[
\ell_{13}^{0}(x)=1-\min(1,\tfrac32(1-b_0(x)))
=(\tfrac32 b_0(x)-\tfrac12)_+
\le\min\left(1,\frac{(L(x)-2)_+}{4}\right).
\]

Consequently, for the actual unnormalized prefix `lambda11`,

\[
\Delta_{13}^{0}\le C(u,v):=
\int\min\left(1,\frac{(L-2)_+}{4}\right)d\lambda_{11},
\quad u=5^{-H5},\quad v=7^{-H7}.
\]

This bound permits arbitrary overlap, current phases and finite heights. It bounds the actual union loss, rather than interpreting a count overload or a query supremum as an attained row loss. It is only the first part of the estimate for the full row; the other cofactors are charged below.

## Four corners cover all independent heights

Only the zero coarse residue modulo `p^4` can encounter comb teeth above height four. Within that residue the remaining comb tail has conditional mass

\[
\frac{1-p^4p^{-Hp}}{p-1}.
\]

The mass of each complete old5 signature is affine in `u`, and each old7 signature is affine in `v`. The old survivor weights are products of these masses. The fixed first11 allowed fibres, PA densities and query signatures depend only on coarse residues; they do not depend on `H5,H7`. Hence `lambda11(1)`, `C(u,v)`, the query hinge and the old mass are bilinear in `u,v`. The PA auxiliary hinges are separately affine in the actual pure masses

\[
x=\tfrac12+\tfrac u2,\qquad
y=\tfrac23+\tfrac v3,
\]

so `F11,F13`, `S11`, and the NC4 old credit are bilinear too.

Define

\[
\delta(u,v)=\mathrm{credit}(u,v)+S_{11}(u,v)
+\tfrac14 F_{13}(u,v)-C(u,v)-k_{\rm req}.
\]

The four exact corner values are:

| `u` | `v` | Exact `delta(u,v)` |
|---|---|---|
| `0` | `0` | `111772630290898924452813601 / 37646391762099329385496320000` |
| `0` | `1/2401` | `14643762790009180541365081 / 4802038164889330440275200000` |
| `1/625` | `0` | `134396669342248830475869307373 / 37960111693450157130375456000000` |
| `1/625` | `1/2401` | `8085496613032965340963987919 / 2232947746673538654727968000000` |

Here `u=0` or `v=0` is an algebraic endpoint of the affine mass formula; no infinite original family is used in the conclusion. Each finite-height value is a convex combination of the four corners, with weights `(1-625u)(1-2401v)`, `(1-625u)2401v`, `625u(1-2401v)`, and `625u2401v`. In particular

\[
\delta(u,v)\ge\delta_*:=
\frac{111772630290898924452813601}
     {37646391762099329385496320000}
=0.002969013099508424\ldots>0.
\]

The exact polynomial is

\[
\begin{aligned}
\delta(u,v)=\delta_*
&+\frac{4648414385484088925560484221}{13014895437754339587557299200}\,u\\
&+\frac{916462793509847006871175289}{4743037695974613552316800000}\,v\\
&+\frac{14723709929815524509}{196327943125145694720}\,uv.
\end{aligned}
\]

All coefficients are positive. This is an exact all-height calculation, not an extrapolation from finitely many tested heights.

## Charge every other old cofactor on the same source

For `d=5^a 7^b 11^c`, every old cylinder has actual pre13 mass at most

\[
c_d(x,y)=
\begin{cases}x&a=0\\5^{-a}&a>0\end{cases}
\begin{cases}y&b=0\\7^{-b}&b>0\end{cases}
\begin{cases}1&c=0\\(5/3)11^{-c}&c>0.\end{cases}
\]

For `c=0`, use the actual first11 fibre mass bound one. For `c>0`, use the same kernel's density cap `5/3`. The raw old5/7 source is a restriction of the actual pure-product source. Thus these bounds hold for all phases on this one actual `lambda11`, without assuming that its coordinates are independent.

Let `b13` be the forbidden fraction of the full actual row and `b0` the
retained subunion defined above. On every same pre13 history,

\[
0\le b_{13}-b_0\le
\sum_{i\text{ outside the retained cofactors}}
13^{-e_i}\mathbf1_{[r_i]_{d_i}}.
\]

This partitions the actual originals for an inequality; it does not replace
the final actual kernel or the pre13 source.
The fibre-loss function `(3b/2-1/2)_+` is `3/2`-Lipschitz. One additional original at `d*13^e` therefore increases integrated row loss by at most `(3/2)13^-e c_d(x,y)`. There are at most two copies per full label, so the entire finite inventory outside `D17` and the unit costs at most

\[
B(x,y)=\frac14\left[
(x+\tfrac14)(y+\tfrac16)\tfrac76-xy
-\sum_{d\in D_{17}}c_d(x,y)\right].
\]

This is a sum of nonnegative caps for omitted cofactors, so it is increasing in `x,y`. With `x<=313/625` and `y<=1601/2401`,

\[
B(x,y)\le B_*:=\frac{292154333}{104587560000}
=0.0027933946733244373\ldots.
\]

This charges arbitrary phases and all finite heights outside the 17 specified old cofactors, including cofactors outside the original 125-label box. The actual full row consequently satisfies `Delta13 <= C(u,v)+B*`. The strictly positive remaining uniform margin is

\[
\delta_{17}:=\delta_*-B_*
=\frac{264456002910627022478441}{1505855670483973175419852800}
=0.00017561842618398643\ldots>0.
\]

## Consume the margin on the same complete PA law

Use the existing [NC4 identity](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md#necessary-query-carriers-and-actual-pure-labels-for-the-remaining-lower-target)
and its [same-law saving form AM8](566-a-mixed-free-first-eleven-slot-closes-the-common-query-law.md#3-same-row-loss-and-the-complete-query-consumer).
Here `credit` is the old pure/mixed contribution in mass-saving units,
`F13` is the complete auxiliary threshold-two hinge before13, and
`Phi` is the final complete auxiliary threshold-three hinge. They are
computed under the same actual pure-source parameters `x,y`. In particular,

\[
k_{\rm req}=\frac{6168733163201163811}{1650097635185615616000},
\quad
(T-2)\lambda_{\rm final}(1)-\Phi
=(T-2)(\mathrm{credit}+S_{11}+S_{13}+S_{17}+S_{19}-k_{\rm req}).
\]

The later17/19 savings are nonnegative. Since

\[
S_{13}=F_{13}/4-\Delta_{13}\ge F_{13}/4-C(u,v)-B_*,
\]

one has

\[
(T-2)\lambda_{\rm final}(1)-\Phi
\ge(T-2)\delta_{17},\qquad T=257/51.
\]

The same bilinear corner evaluation gives

\[
\lambda_{\rm final}(1)\le\lambda_{11}(1)
\le M_*:=\frac{1272755929}{5991995625}.
\]

The existing complete-query comparison, followed by one final normalization and label exhaustion, therefore yields

\[
R_Q\le T-\frac{(T-2)\delta_{17}}{M_*},
\]

which is the stated bound. This uses the same actual source and all the actual later kernels.

For the more restricted special case where every row13 cofactor lies in the 125-label box and every old projection is `r_d`, there is no extra debit. The stronger bound is then

\[
R_Q\le T-\frac{(T-2)\delta_*}{M_*}
=\frac{723076773409562131436960097257}{144709874209547238079280572416}
=4.996734171453361\ldots.
\]

## Finite windows suffice: every outside original is arbitrary

A second consumer removes all prescribed infinite comb continuations and
all high13 projection restrictions. Keep the complete original family
finite, Q-smooth, and at most two copies per full numerical modulus.
Impose only these finite-window conditions:

1. At old labels `5^a7^b` with `0<=a,b<=5`, excluding the unit, retain
   exactly the70 pure/mixed originals specified at the beginning with
   `H5=H7=5`.
2. At labels `5^a7^b11^c` with `0<=a,b<=4` and `1<=c<=4`, retain
   exactly the200 originals from Report558's table. Every numerical
   cell of this window has its two prescribed occurrences.
3. For each `d` in `D17` and `1<=e<=4`, any original at `d*13^e`
   must have old projection `r_d`. Such originals need not be present;
   their multiplicities and current13 phases are arbitrary within the
   common two-copy rule.

Every other original, including all old labels outside the old window,
all first11 labels outside its window, all higher13 projections, all
pure13 originals, and every17/19 original, may have arbitrary globally
fixed phases and arbitrary finite heights. In particular this class has
only68 constrained row13 numerical labels, rather than a restriction at
all heights of each of17 cofactors. It satisfies

\[
R_Q\le
\frac{6065177817620522505771624823623547}
     {1203623046973730557227795845376000}
=5.039100765700856\ldots<257/51.
\tag{FW1}
\]

The70+200 prescribed originals are precisely the finite source of
Report558 Section6. The theorem concerns all the continuations above,
not just that one finite configuration. The earlier all-height theorem
also covers shorter old combs; the present theorem has its own stated
finite-core hypotheses.

### A joint score avoids separating losses from retained mass

Let `lambda0` be the complete actual old survivor restriction and let
`lambda11`, `lambda13` be its actual PA prefixes. Let `x,y` be the
complete actual pure5/7 survivor masses and `m=xy-lambda0(1)`.
With `P(x,y)` denoting the pure-anchor part of `credit`, set

\[
A(x,y)=P(x,y)+\frac1{12}-xy+\frac{F_{11}(x,y)}3
                                      +\frac{F_{13}(x,y)}4.
\]

The definitions give the exact cancellation

\[
\mathrm{credit}+S_{11}+S_{13}=A(x,y)+\lambda_{13}(1).
\tag{FW2}
\]

Indeed `credit=P+1/12-m`, `S11=F11/3-lambda0(1)+lambda11(1)`
and `S13=F13/4-lambda11(1)+lambda13(1)`.
Both the mixed deletion mass and the intermediate11 mass cancel.
Retaining the70 old originals gives

\[
\tfrac12\le x\le x_5:=1563/3125,\qquad
\tfrac23\le y\le y_5:=11205/16807.
\]

The exact PA formulas make `A` bilinear. Its slope in each variable is
negative at both endpoints of the other variable's interval, so
`A(x,y)>=A(x5,y5)`. The four exact values are retained in the data.

### Transport a bounded payoff through added originals

Let `lambda0,ref` and `lambda11,ref` use only the70+200 prescribed
originals, and put

\[
f=1-\min(1,(L-2)_+/4),\qquad 0\le f\le1.
\]

Additional old originals give `lambda0<=lambda0,ref`.
For an11-fibre whose allowed set shrinks from `G` to `G'`, write
`h=min(5/3,1/H(G))` and `h'=min(5/3,1/H(G'))`, with density5/3
at zero allowed mass. Since `h'>=h`, the negative variation of the
kernel change is supported on `G\G'` and has mass

\[
\int(h\mathbf1_G-h'\mathbf1_{G'})_+
=h\,H(G\setminus G')\le\tfrac53 H(G\setminus G').
\tag{FW3}
\]

The bounded nonnegative payoff can therefore lose at most this amount.
An old history removed before11 costs at most its old mass because the
reference11 kernel has total mass at most one. The same source argument
as the complement estimate above gives

\[
\lambda_{13}(1)\ge\lambda_{11,\mathrm{ref}}(f)
                  -D_0-\tfrac53 J_{11}-J_{13}.
\tag{FW4}
\]

Here `D0` pays additional old originals, `J11` pays added first11
forbidden fractions, and `J13` pays every row13 original except the
pure originals and the constrained finite-core projections. These are
bounds for one actual process. The reference measure only supplies a
comparison payoff; the final law uses all actual kernels.

### Complete complementary sums

Set `U=x5+1/4`, `V=y5+1/6`,
`t5=1/(4*5^5)` and `t7=1/(6*7^5)`. Raw pure-source cylinder caps give

\[
D_0=2(t_5V+t_7U-t_5t_7)=\frac{93413}{630262500}.
\]

For the first11 window put
`a=1/(4*5^4)`, `b=1/(6*7^4)`, `c=1/(10*11^4)`. Then

\[
J_{11}=2\left[\frac{aV+bU-ab}{10}+(U-a)(V-b)c\right]
       =\frac{718178719}{8388793875000}.
\]

The first summand counts every outside old cofactor at all11 heights;
the second counts higher11 exponents inside the old cofactor box.
They are disjoint. Actual pure masses are at most `x5,y5`, so these
same caps dominate all added originals, whatever their phases.

Use the earlier `c_d(x,y)` raw actual-prefix cap and let
`K17=sum_(d in D17)c_d(x5,y5)`. All pure13 originals remain in the
retained subunion. The other row13 originals cost at most

\[
J_{13}=\frac14\left[\frac76 UV-x_5y_5-K_{17}\right]
             +\frac{K_{17}}{4\,13^4}
       =\frac{292309125085163}{104549385540600000}.
\]

The first term pays all other nonunit cofactors at all13 heights; the
second pays the17 retained cofactors above current height four. Thus
nothing outside the finite restrictions is omitted. Every sum is a
convergent upper bound for an arbitrary finite actual inventory.

The independently checked height-five baseline supplies

\[
A(x_5,y_5)+\lambda_{11,\mathrm{ref}}(f)-k_{\rm req}
=\frac{1370588963644965884709218881427}
       {442867969756918499854380320000000}.
\]

Subtracting all three debits in FW4 leaves

\[
\delta_{\rm FW}
=\frac{46107017007224922814812136151}
       {5757283606839940498106944160000000}
=0.000008008467214025637\ldots>0.
\]

Every actual11 fibre has total mass `min(1,5H(G')/3)`, which can only
shrink when originals are added. Along with the old-source inclusion,
this gives

\[
\lambda_{\rm final}(1)\le\lambda_{11}(1)
\le\lambda_{11,\mathrm{ref}}(1)
=\frac{19543635187}{92276732625}.
\]

FW2--FW4 and the nonnegative actual17/19 savings now give
`(T-2)lambda_final(1)-Phi >= (T-2)delta_FW`. The complete-query
comparison and one final normalization prove FW1, at every query height.

## Boundary of the result

The opening theorem retains its17 old-projection restrictions, prescribed old combs and fixed first11 table. The finite-window theorem instead retains exactly its stated70+200 core and68 finite projection conditions. Removing one of these hypotheses requires another estimate; the present calculation does not prove an unrestricted result. Different old projections outside the 17-cofactor set are already allowed and are paid for by the complement debit.

Report558's H5 two-row-supremum counterexample remains valid. At that finite source, the fixed-query count hinge can obstruct a universal lower bound based only on the untruncated hinge. The present result shows why that obstruction does not automatically become actual row13 loss for this inheritance: one row loses at most all the mass of a fibre.

## All scalar hinge bounds and the actual prefix mass still allow the full charge

The fixed-query clipping improvement above uses the actual joint source.
It cannot be obtained merely by adding every scalar PA hinge bound to
the known prefix mass. The following exact relaxation identifies that
method boundary throughout the full pure-parameter rectangle.

Let `mu=pi5 tensor pi7 tensor pi11` be the complete unnormalized PA
auxiliary count law before13. Its total mass is `xy`, with
`1/2<=x<=1`, `2/3<=y<=1`. Its coordinate masses are

\[
\pi_p(1)=w_p-C_p/p,\qquad
\pi_p(n)=C_p(p-1)/p^n\quad(n\ge2),
\]

where `(w5,w7,w11)=(x,y,1)` and `(C5,C7,C11)=(1,1,5/3)`.
Write `F(t)=integral(M-t)_+ dmu`. All heights remain in this law.
In this section `F(2)=F13`; it is not the earlier first11 hinge.

For a fixed mass `m` in the entire interval

\[
A_{11}:=xy-\tfrac1{12}-\tfrac13(x/42+y/20+59/840)
\le m\le xy,
\]

consider all nonnegative measures `rho` on the positive integers
which have mass `m` and satisfy

\[
\int(L-t)_+\,d\rho\le F(t)\qquad\text{for every real }t.
\tag{SC1}
\]

The actual `lambda11` mass lies in this interval. This scalar
relaxation, however, does not require a load measure to arise from
a single fixed query on that actual source. Its exact optimum is

\[
\sup_\rho\int\min(1,(L-2)_+/4)\,d\rho=F(2)/4.
\tag{SC2}
\]

The upper bound follows directly from (SC1) at `t=2`. For equality use
the two-atom measure

\[
\rho\{4\}=F(2)/2,\qquad
\rho\{1\}=m-F(2)/2.
\tag{SC3}
\]

The following three functions are bilinear in `x,y`. Their four exact
corner values are positive:

| `(x,y)` | `A11-F(2)/2` | `F(1)-3F(2)/2` | `F(3)-F(2)/2` |
|---|---|---|---|
|`(1/2,2/3)`|`229/2016`|`49/480`|`12109/554400`|
|`(1/2,1)`|`1871/7392`|`857/5280`|`41959/2032800`|
|`(1,2/3)`|`851/2016`|`277/1440`|`10859/554400`|
|`(1,1)`|`16123/22176`|`4381/15840`|`105827/6098400`|

Thus (SC3) is nonnegative throughout the rectangle. Its stop-loss
values at thresholds1,2,3 are respectively `3F(2)/2`, `F(2)`, and
`F(2)/2`, bounded by the corresponding complete auxiliary hinges.
At4 its value is zero. Both stop-loss functions are affine between
successive integer thresholds, so these comparisons cover `1<=t<=4`.
For `t>=4` the witness has zero stop-loss. For every `t<=1`, including
negative thresholds, the auxiliary-minus-witness difference is

\[
F(1)-3F(2)/2+(1-t)(xy-m)\ge0.
\]

This proves (SC1) for all real thresholds. The clipped payoff is zero
at1 and `1/2` at4, proving equality in (SC2). The argument concerns
the stated stop-loss constraints; unequal total masses do not justify
comparison for arbitrary signed convex functions.

At the literal height-five source, `m=19543635187/92276732625`, and
(SC3) has weights

\[
\rho\{4\}=\frac{16293608641}{166389300000},\qquad
\rho\{1\}=\frac{25217931347629}{221464158300000}.
\]

Its clipped value is `16293608641/332778600000 = 0.04896230899763386...`.
The required two-row saving cut on that same source is only

\[
\mathrm{credit}+S_{11}+F_{13}/4-k_{\rm req}
=\frac{649004327923538200529792761}
       {14267500448564292689760000000}
=0.04548829910770012\ldots .
\]

Hence even the full scalar hinge profile and the exact actual mass do
not imply the desired clipped improvement. This is an obstruction to
that relaxation, not an actual query attaining its optimum, an actual
row13 loss counterexample, or a failure of the PA law. The fixed query
used earlier has smaller clipped loss precisely because more of its
joint realization was retained. Extending that success to arbitrary
queries or to different query slots requires additional common-source
incidence constraints. Nor can clipped bounds for separate slots be
averaged through Jensen: this clipped payoff is not convex.

The general scalar-majorant method and abstract saturation witnesses
already occur in [Report21](../001-064/21-physical-and-killed-kernel-comparisons-at11-and13.md)
and [Report243](../193-256/243-all-original-j-costs-have-exact-moment-envelopes-and-a-method-boundary.md).
Here the calculation resolves the particular first13 clipped-payoff
relaxation, including all thresholds and all actual pure parameters.
The [exact producer](../../frontier/cover-geometry/first13_scalar_clipping_boundary.py)
and [data](../../frontier/cover-geometry/first13_scalar_clipping_boundary.json)
verify the corner inequalities and the H5 consumer in36 explicit checks.
The all-real and all-parameter claims are supplied by the proof above;
no Lean verification is claimed.

## An actual fixed query also crosses the clipped cut

The preceding abstract relaxation has a separate, actual-source
counterexample to a stronger proposed shortcut. On precisely the
Report558 height-five source, let

\[
C(L):=\int\min(1,(L-2)_+/4)\,d\lambda_{11},\qquad
c_*:=\mathrm{credit}+S_{11}+F_{13}/4-k_{\rm req}.
\]

The assertion `C(L)<=c_* for every finite fixed old query L` is false.
Keep all70 old originals and all200 first11 originals unchanged,
with their literal phases. One query with51 nonunit numerical cofactors,
each with one globally fixed CRT phase, and the unit included once, gives

\[
C(L)=\frac{8639521551969395023}{189903125774875012500}
     =0.04549436201598552\ldots,
\]

\[
C(L)-c_*
=\frac{8055203649533692011747669319}
       {1328603909270755499563140960000000}
=0.000006062908285400902\ldots>0.
\tag{AC1}
\]

The [literal query and exact verifier](../../frontier/cover-geometry/first13_actual_clipped_query.py)
and its [rational data](../../frontier/cover-geometry/first13_actual_clipped_query.json)
specify every cofactor, full CRT residue and load mass. The query contains
all47 nonunit labels `5^a 7^b 11^c` with `0<=a,b<=3`, `0<=c<=2`,
together with the four labels

| Cofactor | Exponents `(a,b,c)` | CRT phase `(r5,r7,r11)` |
|---|---|---|
|625|`(4,0,0)`|`(184,0,0)`|
|6875|`(4,0,1)`|`(49,0,0)`|
|75625|`(4,0,2)`|`(49,0,0)`|
|4375|`(4,1,0)`|`(45,6,0)`|

The other47 phases are also fixed before evaluation, not selected at
individual old histories. Completing this query to any larger finite
box by arbitrary fixed phases cannot decrease `C`, since its payoff is
increasing. No query label is inserted into the original family.

### Exact common-source computation

Enumerate the pure-surviving coordinates modulo `5^5` and `7^5`,
retaining for each coordinate its old mixed-comb status, all50 first11
slot incidences, and all51 query incidences. Intersect the two incidence
masks and remove histories where both mixed-comb flags hold. For each
resulting profile retain its count `n`, active color mask `A`, and query
incidence mask. This is exact finite compression of one joint source.

Write `k=|A|`. The first11 allowed fraction and density are

\[
g_k=1-1464k/14641,\qquad h_k=\min(5/3,1/g_k).
\]

The number `n_A(z)` of allowed full eleven-words over `z mod121` is
zero when the first non-10 digit among its two digits belongs to `A`;
it is `121-12k` at `z=120`, and121 otherwise. These counts retain the
original combs through height four, including over the unresolved
two-digit branch. The verifier also obtains them by enumerating all
14641 full words against the literal original combs. Thus

\[
C(L)=\sum_{\text{profiles}}\frac{n}{5^5 7^5}
       \frac{h_k}{14641}\sum_{z=0}^{120}n_A(z)
                     \min(1,(L(z)-2)_+/4).
\tag{AC2}
\]

All summands are rational. Their unweighted total is the same actual
prefix mass `19543635187/92276732625`. The exact PA formulas reconstruct
the cut `c_*` above and put this source strictly inside the joint NC4
necessary region. Equation (AC2) proves (AC1) without replacing the
source by independent marginal laws.

This refutes a uniform clipped-query bound even on the fixed source.
It does not contradict either theorem above: those theorems retain
their specified17 old projections, whereas (AC1) concerns a different
query. It does not identify `C(L)` with an actual row13 loss, prove
failure of the PA law, or produce an odd cover. Actual row13 originals
must still satisfy their common current-coordinate unions across slots
and heights. Those additional joint constraints are absent from this
single-query shortcut. The earlier abstract optimum `F13/4` is still
not claimed to be realized by any actual query.

## Exact verification

The [standard-library producer](../../frontier/cover-geometry/row13_seventeen_projection_clipping.py)
writes [exact rational data](../../frontier/cover-geometry/row13_seventeen_projection_clipping.json).
It reconstructs the literal first11 table, scans all coarse old residues,
evaluates the actual first11 response, reconstructs the full PA auxiliary
hinges without dropping their tails, and computes the17 explicit old CRT
phases and complete complement debit. It also checks the finite-window
joint-score cancellation, offset monotonicity and all three complete
complement sums. All88 explicit checks passed with
Python optimizations enabled. Its checks include the independently
computed height-five witness and the exact bilinear interpolation there.

The all-height conclusion is supplied by the affine coordinate-mass argument
and convergent complement bound above. Finite checks verify their arithmetic;
they do not substitute for those arguments. No Lean was added or run.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/row13_seventeen_projection_clipping.py
```

The17 prescribed projections are a sufficient restriction within this
construction, not a claim of17 DP states or a globally minimal boundary.
The two-copy, fixed-prime route is a sufficient research route toward the
original covering problem; it is not an equivalence to unrestricted Erdős#7.

The actual51-query counterexample has its own standard-library exact
verification, including all CRT phases, the complete height-four11
comb projection, the full load histogram and the same-source cut:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/first13_actual_clipped_query.py
```
