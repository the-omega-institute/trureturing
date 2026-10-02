# Eight small primes with local ternary depth two admit every prime tail above2000

Let C be any finite family of pairwise-distinct odd numerical moduli greater
than one, with one globally fixed residue for each modulus. Let R be ALL
actual support primes at most2000. Assume |R|<=8, and assume only that every
original whose complete support lies in R has v3(m)<=2. Then C is
noncovering. The construction below leaves distorted survivor mass greater
than1/5000.

Originals using a prime above2000 may have arbitrary ternary depth, arbitrary
other finite exponents, arbitrary mixed support and any finite number of
such tail primes. The conclusion does not identify1/5000 with Haar density.
No Lean verification or resolution of unrestricted Erdős#7 is claimed.

The source argument extends [Report707's shared numerical-label support
response](../700-749/707-shared-support-avoidance-closes-twelve-height-one-primes.md)
from two roots to five depth-two ternary leaves. A one-clique argument below
supplies its necessary signed Shearer premise; fixed leaf weights retain
separate concavity. The final continuation uses [Report734's same-source
fourth-moment tail](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md).
All nonternary old exponents are unrestricted. This differs from a statement
that also bounds the other old exponents by one.

## 1. One actual five-leaf source and completed star cap budgets

First use the benchmark head

    P=(3,5,7,11,13,17,19,23),       Q=P minus{3}.

Avoid the actual pure3 original. If its numerical label is absent, impose
one phase at that unused label solely as a source restriction. Avoid the
actual pure9 original if it removes a new leaf. If9 is absent or its class
already lies within the excluded first root, remove one additional nine-leaf
as a source-only mark. This does not add a second original with label9.
There remain five live nine-leaves, in root groups

    A={0,1},     B={2,3,4},

of sizes two and three. The names denote actual surviving prefixes, not
altered original phases. Give these leaves the fixed weights

    w=(33,33,28,28,28)/150
      =(11/50,11/50,14/75,14/75,14/75),                  (D1)

and give every ternary suffix above depth two independent Haar law.

For q in Q, let Sq be the actual survivor of all pure q-power originals,
and normalize its restricted Haar measure to lambdaq. The finite distinct
pure inventory implies

    Hq(Sq)>=(q-2)/(q-1),
    lambdaq(a mod q^e)<=Cq q^-e,
    Cq=(q-1)/(q-2),       bq=1/(q-2).

The complete cap sum for the actual3q^e star inventory is at most bq.
The same is separately true for the actual9q^e inventory. Sum each original
cap only in its actual surviving root or leaf. Complete these two cap
budgets independently to bq, writing

    u_qA+u_qB=1,       sum_l v_ql=1,
    m_ql=1-bq(u_q,group(l)+v_ql)>=1-2bq>0.              (D2)

Unused budget can be assigned arbitrarily. This completes bounds; it adds
no original congruences and changes no phases. On leaf l let S_ql be the
actual q-star survivor under lambdaq. Its mass is at least m_ql. Define

    sigma_ql=[m_ql/lambdaq(S_ql)] lambdaq restricted to S_ql.

Thus sigma_ql has EXACT mass m_ql and is dominated by lambdaq. All its
actual star exclusions hold. This downscaling is essential: a signed lower
response can be negative, so an unknown larger star mass could not simply
be replaced by its lower bound inside that signed response.

Our star source is the weighted sum, over the five actual leaves, of
product_q sigma_ql. It is dominated by the one product measure

    lambda=weighted ternary law tensor product_q lambdaq.             (D3)

Every operation here uses the original common family. Nothing is chosen
in response to a later query.

## 2. Mixed-support events retain three shared inventories

Fix D subset Q with |D|>=2, and put b_D=product_(q in D)bq. The actual
original labels having this nonternary support split into three inventories:

    d,       3d,       9d.

Each uses the full nonternary exponent vector of d and has complete cap sum
at most b_D. The3d inventory has one shared root allocation; the9d inventory
has one shared leaf allocation. Complete these cap budgets once globally
for D, obtaining

    x_DA+x_DB=1,       sum_l y_Dl=1.

The union of actual D-originals on leaf l has probability at most

    c_Dl=b_D[1+x_D,group(l)+y_Dl]/product_(q in D)m_ql   (D4)

under the normalized star product. To see this, sigma_ql/m_ql is dominated
by lambdaq/m_ql, and each compatible full cylinder has the product cap.
Summation over full distinct exponent vectors gives(D4). The no3 inventory
is allowed its entire b_D cap on each leaf; its actual phases remain fixed.
Originals whose ternary prefix misses the five leaves contribute zero.

Each event is the actual union of its finite original classes, not an
independently adjustable event on every leaf. Disjoint D depend on disjoint
full q-coordinates, so the support-intersection graph is a dependency graph.
Since m_ql>=1-2bq, uniformly

    c_Dl<=3 product_(q in D)1/(q-4).                    (D5)

## 3. Why every signed leaf polynomial is a valid lower bound

For a finite dependency graph and nonnegative activities c_v, write its
negative-activity independence polynomial as

    Z(A)=sum_(I independent in A)(-1)^|I| product_(v in I)c_v.

We use the ordinary Shearer avoidance theorem in the form already used by
Report707, [Scott--Sokal, Theorem4.1(a)](https://arxiv.org/html/cond-mat/0309352v2).
The following elementary argument verifies its full induced-subgraph
positivity hypothesis where needed; checking a positive top value alone
would not generally suffice.

First suppose every induced polynomial of a base graph is strictly
positive. For any deleted vertex set T the ratio

    r_T(A)=Z(A minus T)/Z(A)

is nondecreasing under inclusion of A. Prove this by induction on the larger
set, adding one vertex v to A. The deletion recurrence is

    Z(A+v)=Z(A)-c_v Z(A minus N(v)).

If v lies in T, the numerator stays fixed and the positive denominator
decreases. Otherwise cross-multiplication reduces the desired inequality
to the induction statement for deletion N(v), comparing A minus T with A.
Both sets are smaller than A+v. This also handles zero activities.

Now add a collection C of event vertices forming one clique. For any
A in the base and C' subset C, independent sets choose at most one vertex
of C', so exactly

    Z(A union C')=Z(A)-sum_(v in C')c_v Z(A minus N(v)).

Divide by Z(A), and use the ratio monotonicity. The result is at least
Z(base union C)/Z(base). Therefore a positive FULL polynomial implies that
all its induced polynomials are positive. Shearer then supplies avoidance
at least that full polynomial. If the full polynomial is nonpositive,
the same numerical lower bound is immediate from probability nonnegativity.
Thus the signed full polynomial is a valid avoidance lower bound in both
cases, provided its clique complement lies in the strict region.

For the support events(D4), take C to be all supports containing coordinate5.
They form one clique. The complement uses only7,11,13,17,19,23. Its total
activity is at most

    3[product_(q=7,11,13,17,19,23)(1+1/(q-4))
         -1-sum_(q=7,11,13,17,19,23)1/(q-4)]
      =184697/233415<1.                                (D6)

A nonnegative activity vector with sum less than one has every induced
polynomial between1 minus that induced sum and1. This follows by induction
from the deletion recurrence, using0<Z(A minus N(v))<=1. Hence(D6) verifies
the base premise uniformly throughout the entire completed star domain.

It follows that on each of the five leaves the FULL signed support
polynomial using(D4) is a valid lower bound, including at profiles where
some other large residual polynomial is negative. No monotonicity of an
arbitrary negative full polynomial is assumed.

## 4. The joint five-leaf response is separately concave

Let nu be the star source(D3) restricted to avoidance of the actual mixed
originals. Multiplying each normalized leaf polynomial by its exact star
mass and adding its weight gives a lower bound for m(nu). Put

    g_l(U)=product_(q outside U)m_ql.

For k disjoint mixed supports with union U, the coefficient after
cancellation of the star denominators is

    b_U sum_l w_l g_l(U)
       product_(D in partition)[1+x_D,group(l)+y_Dl].    (D7)

This expression is affine in each pair of allocation vectors x_D,y_D
separately. Its extrema occur at the ten endpoints(r,t), where all root
budget targets r in{A,B} and all leaf budget targets t in{0,...,4}.
The corresponding leaf coefficient vector is

    c_l(r,t)=1+1_(group(l)=r)+1_(l=t).

For a five-vector h with nonnegative entries define E_k(h) to be the minimum
when k is even, and maximum when k is odd, of

    sum_l h_l product_(i=1..k)c_l(r_i,t_i)

over the10^k ordered endpoint choices. The weights occur ONLY in h.
Let N(h,k) count set partitions into k blocks of size at least two. It obeys

    N(0,0)=1,
    N(h,k)=k N(h-1,k)+(h-1)N(h-2,k-1).

All remaining impossible indices have value zero. A uniform lower response
for the single actual source is

    G=sum_l w_l g_l(empty)
        +sum_(U subset Q) sum_(k=1..floor(|U|/2))
           (-1)^k N(|U|,k)b_U E_k((w_l g_l(U))_l).      (D8)

Separate terms may choose different extrema; this is a lower relaxation
with the correct signs, not a claim that those extrema are simultaneously
attainable by one original family. The actual shared allocations in(D7)
are used before the inequality(D8).

Fix every star allocation except u_q and v_q for one q. Each g_l(U) is
affine in this joint pair. Positive even terms use minima of affine
functions; negative odd terms use negative maxima. Every term in(D8) is
therefore concave in that pair, and so is G. Iterating separate concavity
over the seven q-coordinates shows that its minimum is attained among the
10^7 saturated star vertices:

    u_q=e_r,       v_q=e_t.                             (D9)

No coordinatewise monotonicity of G is claimed or needed. The budget
completion in(D2) was already made legitimate by the actual downscaled
source. Keeping one fixed weight law(D1) is also essential: optimizing the
weights separately at each vertex would not establish this concavity bound.

## 5. Complete exact finite minimum

At a vertex(D9), every term of(D8) has the common denominator

    150 product_(q in Q)(q-2)=1192826250.

After that denominator is cleared, the five entries used for a subset U
are exactly

    (33,33,28,28,28)_l
       product_(q outside U)[q-2-1_(group(l)=r_q)-1_(l=t_q)].

The group S2 x S3 permutes leaves within A and B, preserving both weights
and the response. There are7261 orbits of leaf words of length seven,
with128 independent root assignments per word. Thus929408 canonical
profiles represent all10^7 raw vertices. Burnside gives the independent
leaf-orbit count

    (5^7+3*3^7+2*2^7+3^7+3)/12=7261.

The coefficient choices for k=1,2,3 reduce first to10,55,220 multisets,
then to4,16,48 leaf-permutation orbits. Within each root group, sorting the
h entries and coefficient entries in the same order gives a maximum;
opposite orders give a minimum. This rearrangement evaluates exactly the
original endpoint extrema, not a further inequality.

Complete integer enumeration gives

    min G=2263036/1192826250
         =1131518/596413125
         =0.0018972050623466746...=:m*.                 (D10)

In increasing q order, a canonical minimizing star profile is

    ((B,2),(A,0),(A,1),(A,1),(A,1),(A,1),(A,1)).

All929408 canonical responses are positive. An independently written
exhaustive implementation also verifies the orbit sizes sum to5^7 and
obtains the same minimum. An independent rational consumer evaluates this
minimizer using all ordered10^k coefficient choices and the alternative
minimal-block recurrence

    N(h,k)=sum_(j=2..h)binom(h-1,j-1)N(h-j,k-1).

Consequently one actual unnormalized survivor source nu exists with
m(nu)>=m*. The comparison vertex need not be attained by a finite family.
The proof is the source construction, signed-polynomial validity and
concavity above together with the finite integer comparison; the numerical
comparison alone does not establish those mathematical interfaces.

## 6. Complete fourth-query bound on the same unnormalized source

The domination nu<=lambda from(D3) is retained after mixed restriction.
The ternary source has maximal first-root mass r=14/25 and maximal
nine-leaf mass v=11/50. At depth e>=2 the cylinder cap is v3^(2-e).

For four ordered complete query dictionaries, a compatible tuple of
cylinders intersects in one cylinder at their lcm; an incompatible tuple
contributes zero. The number of exponent quadruples with maximum e is
(e+1)^4-e^4. Summing the ternary caps gives

    1+15r+216v=1423/25.                                 (D11)

Here sum_(e>=2)[(e+1)^4-e^4]3^(2-e)=216. This includes every later ternary
cofactor depth; the old-original depth restriction does not truncate the
query dictionary.

For every nonternary p set

    A4(p)=15t+50t^2+60t^3+24t^4,       t=1/(p-1).

Its factor is1+Cp A4(p). Expanding any four independently phased finite
complete query dictionaries and using the one product domination yields

    integral L1 L2 L3 L4 dnu <= K,
    K=(1423/25) product_(p in Q)[1+Cp A4(p)]
     =83957323825075240180209923/277054053281280000000
     =303035.89797994....                              (D12)

The envelope need not be attained. All queries share nu, its original
phases and its actual source records. We do not normalize nu by its small
mass and do not claim that its normalized full first-query budget is below28.

## 7. Every finite prime tail strictly above2000

Apply Report734 HM7--HM15 at

    k=4,       delta=2/7,       r=21,
    B=2000,    ell=6.

The growth comparison is coefficientwise

    1+(7/5)A4=1+21t+70t^2+84t^3+(168/5)t^4<=(1+t)^21.

The analytic conditions B>=286, ell>=4,3^ell<=B and4ell>=r hold.
Report734's stated Rosser--Schoenfeld prime-product input therefore bounds
the complete same-source tail loss by K tau, where

    tau=(21609/10240)(73/71)^21 [2000/1999^4]
          sum_(j=0..21)21!/[(21-j)!18^j].

Exact rational arithmetic gives

    m*-K tau=0.00022033933017146849...>1/5000.            (D13)

Every original touching the tail is assigned to its greatest tail prime.
Its entire earlier cofactor and its one globally fixed phase are retained;
in particular its ternary exponent may exceed two. Head projections of
such tail originals were never inserted as forbidden head originals.
The actual conditional live kernels from Report734 preserve support outside
all processed originals. The estimate covers arbitrary finite heights and
any finite tail length, with no intermediate primes omitted.

This is a positive distorted measure on the finite CRT carrier determined
by the family, hence an actual uncovered residue and integer. The positive
number in(D13) is not the uniform counting density of that residue set.

## 8. Larger actual primes, missing coordinates and the missing-three branch

When3 is present, pad the complete set R to eight distinct odd primes at
most2000 using primes absent from the original support. This adds coordinates,
not original classes. The resulting increasing list starts at3 and dominates
the benchmark tuple P. Keep the ternary coordinate literally fixed.

At each other coordinate use the existing finite prefix-tree injections
from the benchmark prime to the larger actual prime, as in
[Report462](../450-499/462-the-final-stage-ledger-gives-a-seven-core-common-law.md).
Pull back only the head-only original classes. A pullback is empty or one
cylinder at the same complete exponent vector. Distinct numerical moduli
remain distinct under the one coordinate substitution, and every nonempty
pullback preserves its one actual phase. The ternary bound remains exactly
v3<=2; no different prime is renamed3.

For EACH finite injection choice construct its one benchmark source using
(D1)--(D10), before examining any query. Push this source forward, then
average these pushforwards over the injection choices. Each source has
mass at least m*, so the average does also. Its support avoids every actual
head-only original. A query pulls back to a partial benchmark query, which
can be completed by nonnegative terms. The same holds simultaneously for a
product of four queries, so(D12) survives each pushforward and their average.
No selected injection or source depends on which query is subsequently made.

Injection heights may resolve the entire finite family's prime powers,
including head cofactors of later originals; unused higher digits receive
independent Haar extension. For each fixed source prefix law, averaging
these independent injection extensions gives the corresponding Haar suffix.
Thus the same actual source supports every later finite query, not only
those in the original restricted head. Dummy coordinates may be projected
away. These arguments transport the mass and fourth envelope together;
no unjustified monotonicity of the star-profile response in q is needed.

If3 is absent from R, it is absent from the entire original support, since
3<2000. Use instead the normalized pure-survivor product on the eight
nonternary benchmark primes

    Pno3=(5,7,11,13,17,19,23,29).

With b_p=1/(p-2), the actual mixed-original union costs at most
sum_(|D|>=2)product_(p in D)b_p. Its actual restricted source therefore has

    mno3>=2+sum_p b_p-product_p(1+b_p)
          =299974/530145.

Its complete raw fourth envelope is

    Kno3=product_p[1+Cp A4(p)]
        =7101326389957751920822379861/821055227980138905600000.

At the SAME cutoff2000 and the SAME tau,

    mno3-Kno3 tau=0.5657860157898535...>1/5000.            (D14)

The direct cap factors decrease at larger primes; nonternary dummy padding
handles fewer than eight actual small primes. This branch needs no ternary
restriction and does not import a theorem with a larger hidden cutoff.

## 9. Verification and exact scope

The [C++ producer](../../../frontier/cover-geometry/refined-capped-source/uniform_depth2_source.cpp)
reconstructs the endpoint coefficient orbits,
partition coefficients and the complete canonical vertex enumeration with
integer arithmetic. Its default is the fixed weights33,28 and exhaustive
mode; explicit guards check the canonical counts, global minimum and zero
negative profiles. An optional sampled mode is only a research comparison
and is labelled as such.

The [retained enumeration](../../../frontier/cover-geometry/refined-capped-source/uniform_depth2_source_enumeration.json)
contains the final canonical minimum. The paired standard-library
[Python consumer](../../../frontier/cover-geometry/refined-capped-source/uniform_depth2_source.py)
checks the complete producer
metadata, independently evaluates the minimizing profile with all ordered
endpoint choices, and recomputes(D6) and(D10)--(D14) as exact rationals.
Explicit exception guards remain active under optimized Python. These
checks do not certify arbitrary untrusted producer metadata; the retained
producer run and the separately implemented complete enumeration supply
the full finite comparison. The [exact result](../../../frontier/cover-geometry/refined-capped-source/uniform_depth2_source.json)
retains the rational tail reserve and missing-three branch. Normal and
optimized consumer runs agree. Default execution recomputes and compares
the retained result; explicit output regenerates it.

```sh
clang++ -std=c++17 -O3 -Wall -Wextra -Werror docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/uniform_depth2_source.cpp -o /tmp/e7_uniform_depth2_source
/tmp/e7_uniform_depth2_source > /tmp/e7_uniform_depth2_source_enumeration.json
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/uniform_depth2_source.py --enumeration /tmp/e7_uniform_depth2_source_enumeration.json
```

This result supplies a deeper local ternary head than the height-one source,
with fewer small primes and a different tail cutoff. It leaves open the
removal of the old-head ternary restriction, more than eight actual support
primes at most2000 under this particular theorem, and the unrestricted
odd-covering problem. A small positive source plus a raw fourth tail does
not by itself establish a useful normalized first-query continuation at29.
