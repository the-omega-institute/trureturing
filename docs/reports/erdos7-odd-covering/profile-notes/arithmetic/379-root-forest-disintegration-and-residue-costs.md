[Index](../../marked_head_profile.md) · [Common chain law](376-complete-prime-chain-transport-and-joint-prefix-laws.md) · [Saturated fibres](378-saturated-prime-fibres-and-mixed-tail-incidence.md) · [Original extremal model](../321-384/350-extremal-paired-branch-and-source-support.md)

# Root forests give joint bounds without saturation

The first selected prime need not have a saturated projection. A small
set of its surviving roots, together with all missing roots, can form
the first level of a legal transport tree. Its actual residual fibres
therefore jointly inherit a forest version of the product-tree condition.
Finite LP duality gives one probability on their union, retaining every
other selected prime's full-height prefix bounds.

For the four-root branch at 5, uniformly mixing the six two-root laws
gives a joint 5-by-7 first-prefix bound of 1/6. The first-5 marginal
bound becomes 1/2, so this does not dominate every bound of 376.
Keeping the actual residue assigned to each original gives a stronger
test: the two least expensive root costs, together with the 5-free
cost, must still meet the original mixed-tail covering requirement.

These are ordinary mathematical deductions with exact finite controls.
All laws remain on the original residual, and all original heights and
labels are retained. The resulting necessary conditions do not yet
contradict every possible original palette or settle unrestricted
Erdős #7. No new Lean certification is claimed.

## 1. Selecting a forest of actual first-prime fibres

Assume the minimum-class-count odd whole-cover model of 376. Keep its
actual q-free residual R_q in the full carrier B, its selected chain

    q<p=p_1<p_2<...<p_t,
    lambda_1=q, lambda_i=p_(i-1),
    r=p-q+1, r_i=p_i-lambda_i+1, H_i=v_(p_i)(B).

Let A be the actual first-p projection of R_q and put

    s=|A|, r<=s<=p, ell=s-r+1.                    (RF1)

The lower bound comes from 375. Hence 1<=ell<=s. For any subset
T of A with |T|=ell, the union of T with every missing first-p root
has exactly

    ell+(p-s)=q

members. At each u in T independently choose a complete q-ary
tail tree of depth H_1-1; at each missing root choose such a tree
arbitrarily. Together they form a complete q-ary p-tree. Choose
arbitrary complete lambda_i-ary trees in all other selected coordinates.

By 376 the resulting product meets R_q. A witness cannot lie over a
missing root, and therefore belongs to the actual set

    R_T={x in R_q: x mod p belongs to T}.           (RF2)

This is the forest intersection property: every independent choice of
the tail trees at the roots of T, and of the remaining coordinate
trees, has a common actual witness in their union. It does not say
that each individual root fibre has the same property. Unselected
cofactor coordinates stay attached to that common witness.

## 2. One law on the whole forest preserves the remaining prefix bounds

Maximize sum_x mu_x over nonnegative variables on actual R_T, subject to

    sum_x mu_x<=1,
    mu(first root u, specified p-tail prefix of length b)<=r^(-b),
    mu(specified p_i prefix of length a)<=r_i^(-a), i>1. (RF3)

The second constraint ranges over u in T and 0<=b<=H_1-1;
the third over 0<=a<=H_i. The explicit first constraint is essential:
the separate first-root bounds by themselves allow total mass ell.
The zero vector is feasible and the finite feasible polytope is compact.

Give the global mass constraint dual price w_0>=0. Write C_u for
the capacity-weighted sum of prices in the tail tree at u and C_i
for that in coordinate p_i. At a point x in R_T the dual covering
constraint is

    w_0+f_(root(x))(tail(x))+sum_(i>1) f_i(x_i)>=1. (RF4)

Suppose the dual total cost w_0+sum_u C_u+sum_i C_i were below one.
The weighted-tree lemma of 376 supplies, independently at each u,
a complete q-ary tail tree where f_u<=C_u, and in every other
coordinate a complete lambda_i-ary tree where f_i<=C_i. Section 1
gives an actual common witness, lying over some u in T. At that point

    1<=w_0+C_u+sum_i C_i
      <=w_0+sum_(v in T) C_v+sum_i C_i<1,

a contradiction. The dual solution w_0=1, all other prices zero,
has cost one. Finite linear-programming duality therefore gives an
attained primal value one: there exists a probability mu_T on R_T
satisfying all of RF3 simultaneously.

The same proof includes H_1=1, when every tail tree has depth zero,
and a chain with no other selected coordinate. It neither requires
positive mass at every u nor assigns each u equal mass. This is why
a narrow individual fibre does not invalidate the construction.

## 3. Uniform mixing gives a quantitative joint first-root factor

Choose such a mu_T once for every ell-subset T, and average them with
equal weights to obtain one probability nu on actual R_q. A fixed
u in A belongs to a fraction

    theta=binom(s-1,ell-1)/binom(s,ell)=ell/s       (RF5)

of these subsets. For an actual cofactor modulus m dividing B, define

    alpha=v_p(m),
    c(m)=min({r_i^(-v_(p_i)(m)): i>1, p_i divides m} union {1}).

Every query uses one specified residue and original depths. If alpha>=1,
only subsets T containing its first-p residue can contribute. Within
each of their laws, RF3 bounds its mass both by r^(1-alpha) and by
c(m). Therefore the one averaged law satisfies

    nu(x=a mod m)<=gamma_F(m),
    gamma_F(m)=c(m)                         if alpha=0,
    gamma_F(m)=theta*min(r^(1-alpha),c(m))  if alpha>=1. (RF6)

A query over an absent first root has mass zero. Unselected primes
give further restrictions and cannot increase the query mass. Several
unsaturated coordinates still have only the minimum c(m), not a product
of their separate capacities.

When s=r, ell=1 and theta=1/r. This recovers the k=1 case of 378.
When q=3, p=5 and s=4, ell=2 and theta=1/2. For a chain beginning
3<5<7 the comparison is

| Cofactor modulus | 376 marginal price | Forest price |
|---|---:|---:|
| 5 | 1/3 | 1/2 |
| 25 | 1/9 | 1/6 |
| 35 | 1/3 | 1/6 |
| 175 | 1/9 | 1/6 |
| 245 | 1/9 | 1/18 |

The first-coordinate bound weakens while some joint bounds improve.
One cannot take the smaller entry separately in each row: the two
columns are bounds supplied by different laws. An explicit convex
mixture would instead give the corresponding convex combination of
every price, with a single mixing coefficient for all queries.

## 4. Literal root selection is stronger than its uniform average

Uniform averaging discards useful residue information. For fixed T,
the original forest law mu_T gives price zero to every p-bearing
query whose first-p residue is outside T. For a query inside T it
gives the price min(r^(1-alpha),c(m)). Its p-free query price is c(m).
These simultaneous bounds use one law for the entire collection of
queries.

Apply this to the lexicographically extremal q=3 model of 350 and 378,
with p=5, Q=3^H B and actual first-5 roots A. Write every original
mixed modulus as d=3^e m, e>=1, m>1, gcd(m,3)=1. When 5 divides m,
let u_d=a_d mod 5 be its actual assigned first-5 residue, and set

    g(m)=min(3^(1-v_5(m)),c(m)).

Its original private point shows u_d belongs to A: that point's
cofactor avoids every 3-free original and lies in R_3. Thus there
is no forgotten class at a root outside A.

Let U_rho be the pure-3 tail union in root rho=1,2, as in 378.
Their complement has total root-tail measure

    B_H=(3+3^(1-H))/2.

For any non-pure (rho,t), the active original cofactor APs cover
all of R_3. Define their numerical price totals

    a_rho(t)=sum_(active d, 5 does not divide m_d) c(m_d),
    b_(rho,u)(t)=sum_(active d, 5 divides m_d, u_d=u) g(m_d).

For each fixed T with |T|=ell=|A|-2, apply the union bound under
the single fixed mu_T. It gives

    a_rho(t)+sum_(u in T) b_(rho,u)(t)>=1.         (RF7)

Consequently, letting b_(1)(rho,t)<=...<=b_(s)(rho,t) be the ordered
root costs at that tail,

    a_rho(t)+sum_(j=1,...,ell) b_(j)(rho,t)>=1.    (RF8)

This selects an entire root set for the whole active collection;
it does not choose a separate probability for each AP. At four roots,
the relevant term is the sum of the two smallest root costs. At three
roots, it is the smallest root cost.

## 5. The same original tail budget now sees the residue costs

Integrating RF8 over both non-pure root-tail regions yields the
residue-sensitive necessary condition

    sum_rho integral_(t outside U_rho)
       [a_rho(t)+sum_(j=1,...,ell) b_(j)(rho,t)] dt >= B_H. (RF9)

All functions are finite prefix functions. If a single joint-source
interpretation is desired, choose a minimizing T(rho,t), break ties by
a fixed ordering, sample (rho,t) uniformly on the non-pure region,
and then sample x under mu_(T(rho,t)). This explicitly defines one
probability on the actual product of tail and residual coordinates.
Its cofactor law depends on the tail; it is not original product Haar.
This adaptive kernel also need not have the uniform subset inclusion
frequency ell/s, so RF6 must not be attached to it. Its individual AP
bound retains the indicator that its root belongs to T(rho,t) inside
the tail integral.

A simpler consequence involves whole-original sums. Put

    A_0=sum_(original 3^e m, 5 does not divide m) 3^(1-e)c(m),
    B_u=sum_(original 3^e m, 5 divides m, u_d=u) 3^(1-e)g(m).

Here the sums include only mixed originals, so m>1. For each fixed T,
integrating RF7 and enlarging each active tail set to its full original
prefix of mass 3^(1-e) gives A_0+sum_(u in T)B_u>=B_H. Therefore

    A_0+sum_(j=1,...,ell) B_(j)>=B_H,              (RF10)

where B_(j) are the sorted full root costs. The pointwise integral in
RF9 is no larger than this fixed-root minimum; RF9 therefore retains
additional information about where the original 3-tail prefixes lie.
Finally, averaging the fixed-T inequalities gives

    A_0+(ell/s)sum_u B_u>=B_H,
    sum_(original mixed 3^e m)3^(1-e)gamma_F(m)>=B_H. (RF11)

Thus the averaged forest price follows from the more detailed original
root cuts. No sum over transformed moduli or replacement of 3^(1-e)
by original AP Haar mass 1/d occurs. The missing unrestricted step is
an upper bound on one of these actual selected costs below B_H.

## 6. Verification and reuse

[The exact finite controls](../../frontier/cover-geometry/root_forest_disintegration.py)
check the root-subset frequencies, nonuniform nested weighted-tree
selections, and explicit rational mixtures on three prime coordinates.
The conditional examples retain correlation between the last two
coordinates; their joint mass can exceed the product of their
marginals while satisfying RF6. They also check the minimum-root
selection, its integrated comparison, and the stated old/new prices.
These are controls of the formulas and construction, not realizations
of an unknown extremal odd cover or a substitute for the all-height
LP proof.

The proof reuses 375's root lower bound, 376's actual product-tree
obstruction and weighted-tree lemma, and 378's original mixed-tail
source. A search of the relevant 321--378 reports and the D5 congruence,
tree and coupling interfaces found no forest-conditioned version with
these preserved full-height caps. Existing graphical-forest constraint
theorems concern acyclic event-interaction graphs, not this union of
prime-prefix trees. Finite LP duality and averaging are standard tools;
no literature-priority claim is made. The general construction and
source integration were independently reviewed before these controls.

## 7. Complete-layout second-moment corollaries

The same-law caps also give uniform second-moment bounds. Fix literal
heights `H,K>=1` and a source `R` in `Z/5^H x Z/7^K` meeting every
product of a complete ternary 5-tree and a complete five-ary 7-tree.
Assume at least one first-5 root is absent. No missing first-7 root
or standalone 7-projection condition is needed in this section.

For a supported probability `nu`, let `Gamma_{H,K}(nu)` be the maximum
of `E_nu[(sum_(d|5^H7^K) 1_(x=a_d mod d))^2]` over independently chosen
residues at every divisor, including the constant divisor-one term.
The tree arguments of sections 1--3 use only the stated product-tree
property, so they apply to this abstract source without an assertion
that it is realized by an actual cover.

Put `u_a=2a+1`. If one law bounds every cylinder at depths `(A,B)` by
`M(A,B)`, then its complete-layout moment satisfies

\[
 \Gamma_{H,K}(\nu)\le
 \sum_{A=0}^H\sum_{B=0}^K u_Au_B M(A,B).
 \tag{RF12}
\]

Indeed, two chosen divisor classes intersect either trivially or in
one class at their LCM. There are `u_A` ordered pairs of 5-exponents
with maximum `A`, and `u_B` corresponding pairs of 7-exponents. The
same fixed law bounds all these intersections, including incompatible
layout choices; no product of unconditional marginal probabilities is
used.

The first-5 projection has either three or four roots. RF6, including
its saturated case, supplies one law with

\[
 M_\theta(A,B)=
 \begin{cases}
 3^{-B},&A=0,\\
 \theta\,3^{-\max(A-1,B)},&A\ge1,
 \end{cases}
 \qquad
 \theta=\begin{cases}1/3,&\text{three first-5 roots},\\
                     1/2,&\text{four first-5 roots}.
       \end{cases}
 \tag{RF13}
\]

In particular the exact finite upper expression is

\[
 B_{H,K}(\theta)=\sum_{B=0}^K u_B3^{-B}
 +\theta\sum_{A=1}^H\sum_{B=0}^K u_Au_B3^{-\max(A-1,B)}.
 \tag{RF14}
\]

The infinite sums evaluate to

\[
 \sum_{B\ge0}u_B3^{-B}=3,\qquad
 \sum_{C,B\ge0}(2C+3)(2B+1)3^{-\max(C,B)}=\frac{93}{2}.
 \tag{RF15}
\]

For example, grouping by `m=max(C,B)` gives
`sum_(C,B>=0) u_Cu_B 3^(-max(C,B))=30` and
`sum_(C,B>=0) u_B 3^(-max(C,B))=33/4`; their combination is the
second sum in RF15. Thus, with a single law for all layout phases,

\[
 \Gamma_{H,K}(\nu)\le B_{H,K}(\theta)
 \le3+\frac{93}{2}\theta
 =\begin{cases}37/2,&\theta=1/3,\\105/4,&\theta=1/2.
   \end{cases}
 \tag{RF16}
\]

Consequently every source under this section's hypotheses admits
`Gamma<=105/4`, uniformly in both heights. The law is chosen for the
fixed source; this does not assert one probability realizing unrelated
sources at all heights. The separate law of report 376 gives the
weaker ceiling 30 from `M(A,B)=3^(-max(A,B))`. Its caps must not be
combined pointwise with RF13 as if they belonged to the forest law.

There is also a precise saturation interpolation. If, for some
`1<=k<=H`, the first-5 projection modulo `5^k` has exactly `3^k`
points, report 378's SF6 constructs one law with

\[
 M_k(A,B)=3^{-\min(A,k)-\max((A-k)_+,B)},\qquad
 C_{H,K}(k)=\sum_{A=0}^H\sum_{B=0}^K u_Au_B M_k(A,B),
 \qquad \Gamma_{H,K}(\nu)\le C_{H,K}(k).
 \tag{RF17}
\]

The product factor comes from isolating actual saturated prefixes and
mixing the supported fibre laws. Extending the nonnegative sums to
infinity gives

\[
 \sup_{H\ge k,\ K\ge1} C_{H,K}(k)
 =9+\frac{15k/2+21}{3^k}.
 \tag{RF18}
\]

To verify the expression, the part `A<=k` is
`3(3-(k+2)/3^k)`. After writing `A=k+C`, the remaining double sum,
before multiplication by `3^(-k)`, is
`sum_(C>=1,B>=0)(2C+2k+1)(2B+1)3^(-max(C,B))=27+21k/2`.
Adding the two terms proves RF18. At `k=0`, the same formula denotes
the unsaturated report-376 bound rather than an extra hypothesis.

| Saturated depth `k` | Infinite upper expression |
| --- | ---: |
| 0 | `30` |
| 1 | `37/2` |
| 2 | `13` |
| 3 | `191/18` |
| 4 | `260/27` |

When `k=H`, no first-coordinate tail remains unsaturated. RF17 becomes
`M_H(A,B)=3^(-A-B)` throughout the finite exponent rectangle, and hence

\[
 \Gamma_{H,K}(\nu)\le
 \left(1+\sum_{A=1}^H(2A+1)3^{-A}\right)
 \left(1+\sum_{B=1}^K(2B+1)3^{-B}\right).
 \tag{RF19}
\]

This is a direct corollary of the existing cylinder caps and the LCM
expansion, not a new conditional-law theorem. Full-depth saturation is
an additional sufficient condition, not a consequence asserted for all
product-tree blockers or minimum odd covers. Three roots at depth one
only give `k=1`; their deeper fibres may remain unsaturated. The
unresolved finite comparison therefore includes such three-root sources
as well as four-root sources. No bound with limiting constant 9 for
arbitrary unsaturated sources follows from RF16 or RF18.
