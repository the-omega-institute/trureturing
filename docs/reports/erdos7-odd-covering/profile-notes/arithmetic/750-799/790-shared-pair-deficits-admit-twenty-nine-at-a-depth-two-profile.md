# Shared pair deficits admit29 at a depth-two star profile

Keeping one actual mixed-support allocation across the negative first-order
and positive second-order terms gives a strictly positive correction to the
separate-extrema source bound. At the specified depth-two star profile below,
the corrected survivor mass is at least

    alpha*=134815726597/4496713746525=.02998094479578198... .

The same normalized source has complete first-query bound at most
27.31749784620939..., strictly below28. It therefore admits arbitrary original
moduli ending at29. After every remaining support prime strictly above3000
is included, a distorted survivor measure still has mass greater than1/100.

The old head is literally P8=(3,5,7,11,13,17,19,23). Its originals have
v3<=2 and the star-phase restrictions in Section1; its mixed supports and
nonternary heights are otherwise arbitrary. Originals involving29 or a
prime above3000 have arbitrary fixed phases and all finite exponents. No
support primes31 through3000 are included. This is not a uniform theorem
over arbitrary old star profiles, nor unrestricted Erdős#7. All moduli are
odd, greater than one, pairwise numerically distinct, and retain one globally
fixed residue throughout.

The support-polynomial construction extends the shared-support method of
[Report707](../700-749/707-shared-support-avoidance-closes-twelve-height-one-primes.md).
The uniform depth-two source in
[Report789](789-eight-small-primes-local-ternary-depth-two-and-complete-tail.md)
uses separate extrema; the present fixed-profile refinement retains their
shared allocations.
The complete prime-tail input is [Report734](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md).
The source argument, common-allocation correction and arbitrary-phase query
comparison here are ordinary mathematics with exact rational computation,
not new Lean verification or an external novelty claim.

## 1. The actual source and the stated star contract

Let Q=(5,7,11,13,17,19,23). First avoid the actual pure3 and9 originals.
If a label is absent, or its cylinder has already been excluded, make
additional source restrictions so that exactly five depth-two ternary
leaves remain, grouped as R0={0,1} and R1={2,3,4}. This is a restriction
of a comparison measure, not permission to duplicate a numerical modulus.
For example, excluding0 mod3 and1 mod9 gives leaves(4,7,2,5,8) in that
order. Leaf names below refer to this choice; they do not change phases.

In prime order, require the root/leaf star profile

    (r_q,t_q)=((1,3),(0,0),(0,1),(0,4),(0,2),(0,2),(1,4)).       (PC1)

Concretely, every old original3q^j that meets the retained ternary source
must have ternary root R_(r_q), and every old original9q^j that meets it
must have ternary leaf t_q. Classes disjoint from the retained source
impose no such restriction. There is no condition on their q-adic phases
or finite heights. The actual family must admit the five-leaf choice and
profile(PC1); an arbitrary star family is not asserted to do so.

For each q let S_q be the actual survivor of all pure q-power originals,
and take lambda_q=H_q|S_q/H_q(S_q). Put

    C_q=(q-1)/(q-2),       b_q=1/(q-2).

Distinctness of pure numerical labels gives lambda_q(a mod q^j)<=C_q/q^j
and sum_(j>=1)C_q/q^j=b_q. On the five ternary leaves use

    w=(a,a,b,b,b),     a=6375/23726,     b=5488/35589,    2a+3b=1,

with independent Haar digits above depth2. The one original product law is

    lambda=lambda3 tensor product_(q in Q)lambda_q.

It is fixed before any query. Let U avoid every actual old original and
write alpha=lambda(U). The desired normalized source will be mu=lambda|U/alpha.

On leaf l the actual q-star survivor has lambda_q mass at least

    m_(q,l)=1-b_q(1_(l in R_(r_q))+1_(l=t_q))>0.                (PC2)

If that actual mass is z_(q,l)>=m_(q,l), restrict to the actual survivor
and multiply its measure by m_(q,l)/z_(q,l). This constructs a submeasure
rho_(q,l)<=lambda_q of exactly the mass m_(q,l). Its normalized law has
cylinder cap C_q/(m_(q,l)q^j). The product of these submeasures has exactly
the prescribed star mass and is supported in the actual star survivor.
This works for finite digit spaces as well as Haar spaces; no extra
independence of forbidden events or attainment of a saturated budget is
assumed. In particular, it does not replace a multiplier of a negative
polynomial by a lower bound.

For every nonternary support D with |D|>=2, keep its separate numerical
inventories d,3d,9d, where supp(d)=D. Each inventory has pooled cap
b_D=product_(q in D)b_q. Its actual root and leaf allocations can be
completed upward to simplex vectors x_D on the two roots and y_D on the
five leaves. The one resulting cap vector is

    c_(D,l)=1+x_(D,r(l))+y_(D,l).

Its ten vertex colors are c^(r,t)_l=1+1_(l in R_r)+1_(l=t). The actual
vector has the convex representation

    c_D=sum_(r,t)theta_(D,r,t)c^(r,t),
    theta_(D,r,t)=x_(D,r)y_(D,t),   theta>=0,   sum theta=1.    (PC3)

The same theta_D is used in every occurrence of D. This identity is an
algebraic representation of cap vectors, not a claim that actual root
and leaf inventories are independent. Completing caps adds no original
class and does not change any actual phase.

## 2. Why the full signed source response is valid

On a fixed leaf, under the normalized restricted coordinate product, the
event involving support D has upper probability

    p_(D,l)=b_D c_(D,l)/product_(q in D)m_(q,l)
           <=3 product_(q in D)1/(q-4).

The support-intersection graph is a dependency graph. All supports
containing5 form a clique. On its complement the sum of the displayed
caps is

    3[product_(q=7,11,13,17,19,23)(1+1/(q-4))
      -1-sum_(q=7,11,13,17,19,23)1/(q-4)]
       =184697/233415<1.                                  (PC4)

For completeness, the following one-clique argument permits using the
signed independence polynomial even when its top value is negative.
For graph G and activities p>=0 define

    Z_G(A)=sum_(I independent subset A)(-1)^|I| product_(v in I)p_v.

If every induced Z_G(A)>0, then Z_G(A minus S)/Z_G(A) is nondecreasing
under inclusion of A. This follows inductively from the vertex recurrence
Z(A+u)=Z(A)-p_u Z(A minus N(u)). When u lies in S the numerator is
unchanged and the denominator decreases; otherwise, after cross
multiplication the desired difference is

    p_u[Z(A minus S)Z(A minus N(u))
        -Z(A)Z(A minus(S union N(u)))],

which is nonnegative by the smaller-set induction. All denominators are
positive. A base with sum p_v<1 has Z_G(A)>=1-sum_(v in A)p_v>0 by this
same recurrence: positive induced polynomials are at most1.

Now insert a clique C into this positive base. For A in the base and T in C,

    Z_H(A union T)/Z_G(A)
      =1-sum_(c in T)p_c Z_G(A minus N(c))/Z_G(A)
      >=Z_H(G union C)/Z_G(G).

If the top polynomial is positive, every induced polynomial is positive
and the standard Shearer avoidance bound applies to these upper caps. If
the top is nonpositive, actual avoidance is nonnegative and hence still
at least the top polynomial. Thus the top signed polynomial is a valid
lower bound in either case. Equation(PC4) supplies its required positive
base here.

Multiplying by the exact submeasure masses from(PC2) and summing the
actual leaf weights gives alpha>=S(c). Define

    a_(D,l)=w_l product_(q outside D)m_(q,l).

With only seven nonternary coordinates, at most three supports of size
at least two are pairwise disjoint. The response is exactly

    S(c)=sum_l a_(empty,l)
         -sum_D b_D(a_D dot c_D)
         +sum_(D,E disjoint unordered)b_D b_E(a_(D union E) dot c_D c_E)
         -sum_(D,E,F disjoint unordered)b_D b_E b_F
                       (a_(D union E union F) dot c_D c_E c_F).       (PC5)

All color products are componentwise. The inventory is120 supports,
546 unordered pairs and210 unordered triples. The submeasure construction
is used only to prove the lower bound; the source for subsequent queries
remains the original lambda restricted to U.

## 3. Pair deficits preserve one actual allocation

Let F_D be max_c a_D dot c over the ten colors. For a disjoint pair let
M_DE=min_(c,c')a_(D union E) dot cc', and use the maximum over three colors
for each negative triple term. Applying these extrema separately gives

    G=14490465233/566019912150=.02560062803790533... .

Separate affinity extends these extrema to the completed allocations(PC3).
However, the actual c_D in its first term is the same c_D in every pair.
Define the nonnegative quantities

    d_D(c_D)=b_D(F_D-a_D dot c_D),
    e_DE(c_D,c_E)=b_D b_E(a_(D union E) dot c_D c_E-M_DE).

Dropping only the nonnegative differences between the old worst triple
bounds and actual triple values gives

    S(c)-G>=sum_D d_D(c_D)+sum_(D,E)e_DE(c_D,c_E).            (PC6)

For every disjoint pair allocate d_D/deg(D) and d_E/deg(E), where

    deg(D)=2^(7-|D|)-1-(7-|D|).

These degrees are26,11,4,1,0,0 at sizes2,3,4,5,6,7. Each positive-degree
deficit is allocated exactly once. The eight zero-degree supports have
nonnegative deficits which are discarded; they are never divided by zero.
For each of the546 edges set

    delta_DE=min_(i,j in{0,...,9})[
        d_D(c^i)/deg(D)+d_E(c^j)/deg(E)+e_DE(c^i,c^j)].       (PC7)

The local objective is affine separately in each color. At the one
actual pair c_D,c_E, its value is the convex combination of these100
vertex values with coefficients theta_(D,i)theta_(E,j). It is therefore
at least delta_DE. Different edges need not have compatible minimizing
colors: they supply lower bounds on one common actual evaluation, not a
simultaneously attainable artificial family.

Summing(PC7) gives

    Delta=354546550427/80940847437450=.004380316757876656...,
    alpha>=G+Delta=alpha*.                                (PC8)

There are538 positive edge credits and8 zero credits. The four unsigned
terms of G are, in order,

    83998208/179688861,
    272853286507/566019912150,
    15905611/381158190,
    58029053/37734660810.

This deficit-allocation argument also works on other finite support graphs
whenever nonnegative endpoint shares sum to at most one. The particular
fractions in(PC8), the seven-coordinate signed truncation and the star
contract(PC1) belong only to the present instance.

## 4. Complete queries allow independently chosen phases

A finite complete query has one arbitrary phase a_d for each numerical
divisor d of a finite old-head period, including d=1. Write its load as
L=sum_d 1_(a_d mod d), and let B(mu)=sup_layout integral L dmu, followed
by exhaustion of the finite periods. The law mu is chosen before the
layout. Maximizing separately at each numerical label in a finite period
shows that this is the complete sum of cylinder maxima, including the unit.

There is no requirement that the phases for different d agree. In
particular L is not assumed pointwise bounded by a product of physical
matching-prefix runs. The required comparison follows instead from the
following elementary rearrangement inequality.

For c_i>=0, events A_i with probabilities at most t_i, and real h, put
V=sum_i c_i1_(A_i). Then

    E(V-h)_+=sup_E[sum_i c_i P(E intersect A_i)-hP(E)]
      <=max_(0<=s<=1)[sum_i c_i min(s,t_i)-hs]
      =E(sum_i c_i1_(U<=t_i)-h)_+,                       (PC9)

where U is auxiliary uniform on[0,1]. The last equality holds because
the sum on the right is nonincreasing in U; its positive part is obtained
by an initial interval, with a threshold interval handled by continuity.

Apply(PC9) conditionally, one coordinate of the original product lambda
at a time. At each step the other coordinates supply nonnegative
coefficients, while every query label has its own cylinder in the current
coordinate with the specified cap. Use independent auxiliary uniforms
for successive coordinates. A completed exponent box then factors into
M=product_p(1+J_p), with the nested tails

    Pr(J3>=1)=r=max(2a,3b)=6375/11863,
    Pr(J3>=e)=v 3^(2-e), e>=2,     v=max(a,b)=6375/23726,
    Pr(Jq>=e)=C_q/q^e, e>=1.                             (PC10)

Completing missing numerical labels only increases the nonnegative load.
Monotone convergence gives the all-height hinge comparison

    integral(L-h)_+ dlambda<=E(M-h)_+.

The independent runs in(PC10) describe an auxiliary comparison law, not
the actual query indicators and not the generally correlated survivor mu.
Since mu=lambda|U/alpha, one obtains for h>=1

    B(mu)<=h+E(M-h)_+/alpha.                            (PC11)

This is the full-depth version of the restricted-query mechanism in
[Report528 FC17](../500-549/528-surviving-fibre-credits-control-arbitrary-phases-at-ternary-height-one.md).

At h=18 the complete mean and hinge are

    EM=(1+r+3v/2)product_q C_q=94286848/21175455,
    H18=EM-18+sum_(j<18)(18-j)Pr(M=j)
       =.2793473885620212... .

Only the subthreshold atoms require finite enumeration. The displayed
identity uses the full mean and keeps the entire remaining tail; it is
not a truncation of exponent heights. Exact arithmetic yields

    10G-H18=-.023341108182967918...,
    10(G+Delta)-H18=.020462059395798638...>0,
    B(mu)<=18+H18/alpha*=:B*=27.31749784620939...<28.     (PC12)

The shared deficit credit is what makes this particular comparison cross
the pure-conditioned29 continuation threshold.

## 5. Arbitrary29 originals and the full tail above3000

Take the actual pure29 survivor law rho29, with cap C29=28/27 and complete
inventory b29=1/27. The product mu tensor rho29 already avoids pure29
originals. For each positive29 exponent, every remaining original has
a nonunit old numerical cofactor. Distinct full labels allow one phase
per such cofactor. Equations(PC11)--(PC12) therefore bound their total
deletion by(B*-1)/27. Restricting this same product to the actual remaining
survivor gives an unnormalized measure nu29 with

    mass(nu29)>=(28-B*)/27=:m29=.025277857547800438... .   (PC13)

The old cofactors here may have arbitrary ternary depth. They are queried,
not inserted as extra old forbidden classes. The pure unit cofactor has
already been excluded by rho29, and no further normalization is made.

For complete mixed fourth queries use the same original product source.
At one coordinate, compatible intersections of four cylinders are their
largest-depth cylinder; incompatible intersections are empty. For a cap
tail t_e, the full geometric factor is

    1+sum_(e>=1)((e+1)^4-e^4)t_e.

At3, tails(PC10) give exactly1+15r+216v; at q in Q they give1+C_q A4(q),
where, with t=1/(q-1),

    A4(q)=15t+50t^2+60t^3+24t^4.

Since mu<=lambda/alpha*, all four query layouts obey one joint envelope

    K8=[1+15r+216v] product_(q in Q)[1+C_q A4(q)]/alpha*
      =1068419013913480870613388825227/89669705971802913792000.

The product with rho29, followed by the actual restriction defining nu29,
has complete mixed fourth envelope

    K29=K8[1+(28/27)A4(29)]
       =18370854419091495866842584627592421
         /949064168005562039574528000.                 (PC14)

Mass(PC13) and moment(PC14) refer to the same unnormalized source. Independent
attainment of the cylinder caps is never required.

Apply Report734 HM7--HM15 with delta=2/7, growth exponent21, cutoff3000
and ell=7. Its coefficient comparison and analytic range are

    1+(7/5)A4(p)<= (1+1/(p-1))^21,
    3000>=286,   ell>=4,   3^ell<=3000,   4ell>=21.

The complete prime-tail allowance is

    tau=(21609/10240)(99/97)^21 *3000/2999^4
        *sum_(j=0..21)21!/((21-j)!21^j).

Thus the final distorted survivor mass is at least

    m29-K29*tau=.01032138769537434...>1/100.             (PC15)

The inherited tail comparison assigns each original to its greatest tail
prime and keeps every earlier cofactor, including every finite ternary
height. It allows any finite number of support primes strictly above3000.
Its analytic prime-product premise and attribution remain those of
Report734. Positive supported mass gives an actual finite-CRT survivor;
the number1/100 is not an undistorted Haar-density bound.

## 6. Exact arithmetic and remaining scope

The [consumer](../../../frontier/cover-geometry/refined-capped-source/depth_two_pair_deficit.py)
reconstructs all120 support masks,546 pairs,210 triples and54600 local
vertex objectives. It retains every edge minimum and a minimizing pair,
checks all endpoint budgets, rebuilds the complete H18 from the full mean,
and evaluates the same-source29 and complete-tail inequalities. Its
[result](../../../frontier/cover-geometry/refined-capped-source/depth_two_pair_deficit.json)
contains the exact fractions, including H18 and the final reserve.
The quartic and cutoff arithmetic reuse the existing adjacent
[height-lift consumer](../../../frontier/cover-geometry/refined-capped-source/local_ternary_height_lift.py).

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/depth_two_pair_deficit.py
```

Default execution recomputes and compares the retained result. An explicit
`--write-result PATH` regenerates it. All checks remain active under `-O`.
An independent rational reconstruction agrees with every edge credit,
all four baseline terms and the complete-query constants. These finite
checks verify the arithmetic; the continuum allocation and arbitrary-height
claims use the arguments above.

The reusable improvement is retaining the shared allocation in(PC6), then
spending each first-order deficit only once. Extending it to every star
profile requires a new uniform estimate. This result neither supplies that
estimate nor removes the old ternary-height restriction or the excluded
intermediate primes31 through3000.
