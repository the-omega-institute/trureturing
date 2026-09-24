# Joint root queries allow an all-height old5/7 family beside the star and triangle towers

Let P={3,5,7,11,13,17,19}. Consider any finite family of pairwise distinct
P-smooth numerical moduli greater than one, with globally fixed arbitrary
residues. Pure-prime originals are unrestricted. Every mixed modulus may
have any of the forms

    3^a*q^b,       a,b>=1, q in {5,7,11,13,17,19};
    3^a*5^b*7^c,   a,b,c>=1;
    5^b*7^c,       b,c>=1.

There is no bound on family size or exponent. Its full actual survivor U
satisfies

    H(U)>=517663/8957952>0.

The ONE uniform law rho=H(.|U) has complete nonunit query norm

    R_P(rho)<=43147691740943/4184308853725
             =10.3117846338...<565/51.                (JQ1)

Arbitrary additional distinct originals touching23 or29, and otherwise
supported on P, leave full Haar survivor at least

    2405915052449/655929462988800>0.                     (JQ2)

This extends [report550](550-a-shared-triangle-tower-preserves-one-common-survivor-law.md)
by the entire old5/7 family, with arbitrary phases and heights. The proof
uses joint queries under one actual law; it does not require membership
in the extra entropy/unused-label class G. These are ordinary arguments
and exact finite computations, not Lean verification or unrestricted
Erdős #7.

## 1. A joint-root conditioning bound

For ANY finite distinct-modulus P-smooth family, let S_p be the actual
complete pure-p survivor. Put

    w_p=H_p(S_p)>=(p-2)/(p-1), a_p=1/w_p,
    rho0=product_p H_p(.|S_p), Omega=product_p w_p.

Let ell be the actual union probability of the mixed originals under this
ONE rho0 and suppose s=1-ell>0. The full survivor law is then

    rho=rho0(.|U)=H(.|U).

Every numerical nonunit query d has cap

    max_r rho0([r]_d)<=K_d=d^(-1)*product_(p|d)a_p,
    Rcap=sum_(d>1)K_d=product_p(1+a_p/(p-1))-1.

For each p choose a root cylinder C_p maximizing its probability under
this SAME FINAL rho. This is a finite choice among p roots. Write

    N=sum_p 1_Cp, x_p=rho0(C_p)<=c_p=a_p/p.

For any integer threshold tau>=0, the pointwise truncation
`N<=tau+(N-tau)_+` and nonnegativity give

    sum_p rho(C_p)<=tau+(1/s)*integral(N-tau)_+ d rho0. (JQ3)

Under rho0, and only there, the chosen root events use independent prime
coordinates. Let M be the sum of independent Bernoulli variables with
parameters c_p. Increasing any parameter increases the expected positive
part, so

    integral(N-tau)_+ d rho0<=E(M-tau)_+.             (JQ4)

At tau=1 this is exactly the independent-indicator hinge identity already
used in [report382, PS5](382-prime-star-overlaps-and-no-prime-excess.md):
`E(M-1)_+=sum c_p-1+product(1-c_p)`. For every tau, monotonicity follows
by conditioning on the other indicators; the derivative with respect to
one parameter is the probability that their sum is at least tau. The
selected maximizing queries need not be independent under rho. No such
claim is used.

All remaining numerical labels retain their K_d/s caps. Removing exactly
the seven prime labels from that geometric sum and inserting JQ3--JQ4
therefore gives

    R_P(rho)<=tau+B_tau(a)/s,
    B_tau(a)=Rcap-sum_p c_p+E(M-tau)_+
            =Rcap-E min(M,tau).                     (JQ5)

This bounds a sum of query maxima, all taken under rho. Neither K_d nor
c_p is assumed to be an attained source maximum. Summable geometric caps
justify taking the complete infinite query sum.

For fixed other parameters, differentiate B_tau with respect to a_p.
If M_others is the Bernoulli count omitting p, the result is

    product_(q!=p)(1+a_q/(q-1))/(p-1)
      -Pr(M_others<tau)/p >0.

The first product is at least one, and the probability is at most one.
Thus all complete pure caps may be substituted simultaneously. Choose
tau=2. At those caps, exact evaluation of the128 Bernoulli cells gives

    B_2(a)<=Bmax=3864341559277/1836515055375.         (JQ6)

One can equivalently evaluate
`B_2=Rcap-2+2 Pr(M=0)+Pr(M=1)`. For any arbitrary mixed support, a
sufficient DIRECT-query condition is therefore

    ell<12808334335598/16672675894875
       => R_P(rho)<565/51.                          (JQ7)

This does not assert that every family meets the loss premise, or that
JQ7 alone implies membership in G. The conditional query bounds for
thresholds tau=0,...,7 can all be evaluated; tau=2 gives the smallest
bound at the actual-loss upper estimate used below. No independence is
introduced by conditioning on U.

## 2. A simultaneous old5/7 boundary

For the stated support theorem, first pass to one irredundant core with
exactly the same U. Within each prime, retained pure cylinders are
pairwise disjoint. Removing redundant originals preserves distinct
numerical labels and the allowed support forms. Every removed label
remains included in the complete query norm.

Use this core's complete pure source throughout. All old5/7 originals
together have mass at most

    a5*a7*sum_(b,c>=1)5^(-b)7^(-c)<=1/15.           (JQ8)

At each ternary depth r=1,2,3 distribute every actual original's outside
charge to its own fixed ternary node. Each star role q has total budget
1/(q-2) at that depth; the triangle role has budget1/15. For a modulo27
leaf j, let X_q(j) and Z(j) sum its three ancestor star and triangle
charges. Here 0<=X_q<=3/(q-2)<=1.

Unite all star events on each coordinate before taking products. The
actual simultaneous5/7 avoidance, including the triangle and old5/7
unions, is at least

    max(0,(1-X5(j))*(1-X7(j))-Z(j)-1/15).

The other four prime coordinates remain independent of this5/7 block
under rho0. Thus the actual low-depth avoidance is at least

    Cplus(j)=max(0,(1-X5(j))*(1-X7(j))-Z(j)-1/15)
              *product_(q=11,13,17,19)(1-X_q(j)).    (JQ9)

The old union is charged ONCE. It is one fixed event, evaluated on every
ternary fibre; averaging those conditional bounds does not create a new
copy of its mass. We do not claim its cap or its position can be attained
simultaneously with all the other charge caps.

## 3. The ternary mask and exact off-inclusive optimization

Report550's pure-mask domination applies to JQ9: `g=1-Cplus` is still
nonnegative and nondecreasing in every charge coordinate. The complete
pure ternary tail has scaled mass at most1/2. Its upper envelope is the
mean with half-weight on a minimum g cell. The same deletion of a root,
a middle node and, if needed, a leaf reduces every disjoint pure mask to
one of the two comparison shapes

    I:  (2,3) | (3,3,3);
    II: (3,3) | (2,3,3).

Each has14 leaves. Charges on removed blocks may be moved to a surviving
node at the same depth, increasing g and retaining their simplex budgets.
This comparison is performed on Cplus before making any signed replacement.
The598 disjoint pure3/9/27 masks and both resulting shapes are checked by
the retained driver.

Replace Cplus by the smaller signed expression obtained by removing its
positive part. The four outside factors are nonnegative. For any fixed
half-weight anchor the signed avoidance is separately affine in the21
charge vectors: seven roles at each of three depths. A minimum therefore
occurs when each vector is OFF or its entire cap is placed on one node.
All off choices must remain present; signed costs need not be monotone.

Use role order(5,7,11,13,17,19,T). If A,B,C are the masks at a leaf's
ancestors and `n_e=1_(e in A)+1_(e in B)+1_(e in C)`, its numerator is

    F(A,B,C)=((3-n5)*(5-n7)-nT-1)
               *(9-n11)*(11-n13)*(15-n17)*(17-n19),
    D=378675.                                      (JQ10)

The new minus one in the joint5/7 factor represents JQ8. It is independent
of the three depth allocations. Every leaf numerator is in
[-100980,353430], so the doubled anchored sums safely fit signed32-bit
arithmetic.

The subset recurrence of report550 evaluates, for each node, all disjoint
allocations of its leaf masks; for each root it similarly splits its
middle and leaf masks. Finally it combines disjoint root masks at all
three depths. A subset minimum on the second root's remainder includes
every possibility to leave a role off. Its exact six anchor minima are:

| Shape | Anchor location | Minimum including off | Minimum with all roles on |
| --- | --- | ---: | ---: |
| I | Two-leaf node in first root |2939540|2939540|
| I | Three-leaf node in first root |3003618|3003618|
| I | Second root |3024138|3024138|
| II | First root |3122120|3122120|
| II | Two-leaf node in second root |3186026|3186026|
| II | Three-leaf node in second root |3223414|3223414|

Equality with the all-on result is an output, not an assumption. The
minimum is W=2939540. As an explicit check, use report550's same literal
placement and anchor a0. In its leaf order a0,...,a4,b0,...,b8, JQ10 gives

    250880,185220,171990,171990,158760,
    50490,100980,151470,50490,25245,50490,
    75735,75735,75735.

All are positive, and the doubled anchored sum is2939540. This witnesses
the same minimum for the positive-part RELAXATION. It is not an actual
original-family realization.

## 4. All higher originals and the final common law

After including every old5/7 height already in JQ8, the only unprocessed
mixed originals have ternary height at least4. Under the SAME rho0,
complete geometric summation gives

    star_tail<=7244/227205, triangle_tail<=1/405.

No bound on either outside exponent is imposed. The full actual mixed
loss therefore satisfies

    ell<=1-2939540/(27*378675)+7244/227205+1/405
        =1527182/2044845.                           (JQ11)

This gives s>=517663/2044845>0. The complete pure mass obeys
Omega>=935/4096, yielding the stated H(U) lower bound. Substitute JQ11
in JQ5--JQ6 to obtain JQ1, with exact margin

    565/51-43147691740943/4184308853725
       =9623660209796/12552926561175>0.                 (JQ12)

All queries in JQ1 refer to this one final law. No separately optimized
numerator, denominator or phase table has been substituted.

For the23/29 extension, tensor rho with fresh Haar coordinates. Each added
original keeps its own fixed full label `d*23^j*29^k`, j+k>0. Sum over all
P-smooth d, including unit d. The complete extra loss is at most

    (1+R_P(rho))*sum_(j+k>0)23^(-j)29^(-k)
      <=(1+43147691740943/4184308853725)*51/616.

Its relative reserve is at least2405915052449/37904915498450. Multiplying
by the initial Haar-survivor lower bound proves JQ2. The query bound JQ1
is not asserted for the newly conditioned extended survivor.

## 5. An additional mixed inventory can be included

More generally, start from the support in the theorem and allow further
mixed originals whose numerical labels have total saturated cap

    delta=sum_(extra d) d^(-1)*product_(p|d)(p-1)/(p-2)
      <9623660209796/450162249161625.                (JQ13)

Use the complete pure source of the whole family. The base-support proof
is uniform in that source, while the extra mixed union has mass at most
delta under the SAME source. Hence its total loss is at most JQ11 plus
delta. JQ13 is precisely the available difference between JQ7 and JQ11,
so the direct-query conclusion remains strict. This is a sufficient
condition on the extra numerical inventory, not on separately optimized
residue choices.

As a concrete all-height consequence, one may also allow EVERY old label
7^b*13^c, b,c>=1, with arbitrary globally fixed phases. Its complete cap
sum is1/55, below JQ13. For this enlarged support,

    ell<=1564361/2044845,
    R_P(H(.|U))<=42546650450093/3883788208300
                =10.9549357915...<565/51.

Arbitrary additional distinct originals touching23 or29 still leave
Haar survivor at least1438892043221/2623717851955200>0. This statement
uses the enlarged support's own single uniform full-survivor law and the
same fresh-coordinate union bound; it does not reuse a law that ignores
the new old7/13 originals.

## 6. Verification and remaining scope

The [standalone driver](../../frontier/cover-geometry/all_height_star_triangle_old57_joint_queries.py)
compiles the adjacent [integer optimizer](../../frontier/cover-geometry/all_height_star_triangle_old57_joint_queries.cpp)
in a temporary directory and writes [exact data](../../frontier/cover-geometry/all_height_star_triangle_old57_joint_queries.json).
It uses no old producer or saved result table. The recurrence includes
143327232 middle-node candidates and6122200320 root-convolution candidates,
followed by the off-state subset minima. The driver checks the pure-mask
reduction, the explicit minimizing layout, all128 pure-cap corners,
all eight truncation thresholds through128 Bernoulli cells, and every final
rational constant. The general inequalities JQ3--JQ9 and the signed
extreme-point reduction are ordinary proof obligations, not consequences
of the finite arithmetic checks alone.
All35 driver checks and8 optimizer checks pass. The retained JSON SHA256 is
`07d3f0da379ac83cf6e3266b663943caaa61fb8195888fb87546946ea08eee52`.

A separately written generic tree optimizer reproduces all six minima,
including off states through21-bit subset closure, and independently
reconstructs the positive literal layout. The expected minima were
disclosed; this is source-independent verification, not an outcome-blind
test. Execution from a different working directory through a script path
containing spaces produces the same JSON bytes on the tested macOS host.
Other operating systems were not tested.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/all_height_star_triangle_old57_joint_queries.py
```

Requirements are Python3.10+ and a C++17 compiler. `--compiler` and
`--output` are explicit options. No original-period enumeration or Lean
build was run.

The base theorem still excludes arbitrary other P-smooth mixed supports.
The23/29 extension allows arbitrary P-smooth cofactors only for originals
that genuinely touch23 or29. It does not allow an unrestricted P-only
family or further fresh primes. The joint-root bridge is general, but
an appropriate uniform actual-loss bound for those families is unresolved.
