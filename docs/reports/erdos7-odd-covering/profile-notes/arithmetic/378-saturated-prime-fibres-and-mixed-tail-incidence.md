[Index](../../marked_head_profile.md) · [Full-chain common law](376-complete-prime-chain-transport-and-joint-prefix-laws.md) · [Original extremal model](../321-384/350-extremal-paired-branch-and-source-support.md)

# Saturated prime fibres give joint caps and a mixed-tail dichotomy

The common marginal caps of 376 become genuine joint caps when the
first selected prime projection attains its minimum prefix cardinality.
Each surviving prefix can then be isolated by a legal complete tree.
The corresponding actual fibre inherits the remaining product-tree
obstruction, so the weighted-tree/LP construction applies inside every
fibre. Mixing these conditional laws gives one probability on the
original residual with a product factor for the saturated prefix.

For the minimum odd-cover model at q=3, the first-5 projection has
either three or four roots. Three roots give the new conditional joint
bound. Four roots force at least four active mixed originals on every
root-tail not covered by a pure 3-power, yielding the all-height bound
I_3>=6+2*3^(1-H). The classification behind this dichotomy also gives
the unconditional bound I_3>=35/6+(5/2)*3^(1-H) for H>=2, and I_3>=8
for H=1.

These are ordinary deductions with exact finite controls. They retain
arbitrary original prime support and heights, but do not convert the
new probabilities to original Haar or resolve unrestricted Erdős #7.

## 1. One saturated projection can be isolated at every surviving leaf

Assume a globally minimum-cardinality distinct odd whole cover. For a
support prime q, let R_q be its actual q-free residual in the complete
q-free carrier. Choose a chain q<p_1<...<p_t of support primes and put

    lambda_1=q, lambda_i=p_(i-1) for i>1,
    r_i=p_i-lambda_i+1, H_i=v_(p_i)(Q).

Report 376 proves that the joint projection of R_q meets every product
of complete lambda_i-ary trees of depths H_i in the original p_i trees.
Its weighted-prefix lemma and finite LP duality give a common law with
the marginal prefix capacities r_i^(-a).

Fix 1<=k<=H_1 and assume

    |projection_(p_1^k)(R_q)|=r_1^k.                (SF1)

The one-coordinate duality in 375 says this projection contains the
leaves of a complete r_1-ary depth-k subtree. Equality in SF1 forces
it to be exactly that leaf set A; in particular every node of this
subtree has exactly r_1 children in it.

For each u in A, construct a complete q-ary depth-k tree T_u which
meets A only at u. Along the path to u, select its next child and
all p_1-r_1=q-1 children outside the r_1-tree. Complete the subtrees
below those outside children arbitrarily. At the next node on u's
path repeat the same choice. Every leaf other than u departs from A
at some level. Thus

    T_u intersect A={u}.                            (SF2)

This is a full branching tree with literal original prefixes, not a
point selected independently from the other coordinates.

## 2. The actual fibre inherits all the remaining tree conditions

Let R_u={x in R_q: x=u mod p_1^k}. Below u choose any complete
q-ary tree of depth H_1-k. Extend T_u through the other depth-k
leaves by arbitrary complete q-ary continuations. Also choose any
complete lambda_i-ary tree through each other original coordinate.

The product-tree obstruction supplies a point of R_q in this product.
By SF2, its first prefix must be u. Consequently R_u is nonempty and,
after removing that fixed prefix, meets every stated product of the
remaining tail and coordinate trees. All unselected cofactor coordinates
are still carried by the same actual point.

Apply the same weighted-tree/LP proof as 376 inside R_u. It gives a
probability nu_u on actual R_u with

    nu_u(p_1-tail prefix of depth b)<=r_1^(-b),
    nu_u(p_i prefix of depth a)<=r_i^(-a), i>1.      (SF3)

Depth zero is the root mass constraint; if H_1=k there is no nontrivial
first-coordinate tail. The proof needs no matching integrality and
does not assume independence inside nu_u.

Now define one probability on the original R_q by

    nu=(1/r_1^k) sum_(u in A) nu_u.                 (SF4)

For a present first-coordinate prefix v of depth b<=k, exactly
r_1^(k-b) members of A extend v. Summing their conditional bounds gives

    nu(x=v mod p_1^b, x=c mod p_i^a)
        <=r_1^(-b) r_i^(-a), i>1.                 (SF5)

Absent prefixes have mass zero. This product factor follows from the
explicit fibre construction. It is not obtained by multiplying two
unconditional marginal bounds.

More generally, for any actual cofactor AP of modulus m, put

    alpha=v_(p_1)(m),
    c(m)=min({r_i^(-v_(p_i)(m)): i>1, p_i divides m} union {1}).

Then the same nu satisfies

    nu(x=a mod m)
       <=r_1^(-min(alpha,k))
          min(r_1^(-max(alpha-k,0)), c(m)).         (SF6)

For alpha<=k, sum over the r_1^(k-alpha) extending fibres and use
the other-coordinate bound c(m) in each. For alpha>k, at most one
fibre occurs; inside it take the minimum of the first-tail and other
coordinate capacities from SF3. Unselected primes impose extra
conditions and cannot increase the mass. The usual marginal bounds
are also preserved. Several unsaturated coordinates still cannot
have their bounds multiplied.

## 3. Chain prices for the actual 3-bearing originals

Use the lexicographically extremal model of 350, with divisor closure,
private points, initial-segment odd prime support and normalized prime
classes A_p=0 mod p. Write Q=3^H B. Every mixed 3-bearing original is

    d=3^e m, e>=1, m>1, gcd(m,3)=1.

Its first 3-root is rho_d in {1,2}, its remaining 3-prefix is J_d
of uniform tail mass 3^(1-e), and its full cofactor AP is C_d.
The actual trace is C_d intersect R_3. Every such trace is nonempty:
an original private point avoids all 3-free originals, so its cofactor
lies in R_3. This observation also justifies counting every mixed
original in the incidence below.

For a chosen support-prime subchain P=(s_1<...<s_l) above 3, put
s_0=3 and define

    gamma_P(m)=min({(s_j-s_(j-1)+1)^(-v_(s_j)(m)):
                     s_j divides m} union {1}).    (SF7)

Let U_rho be the union of the pure 3^e tail prefixes, e>=2, in
first root rho. Outside U_rho, the compatible mixed originals
necessarily cover R_3 by their actual cofactor traces. Apply the one
common law supplied by 376 for P and the union bound to obtain

    sum_(d active at (rho,t)) gamma_P(m_d)>=1
                for every t outside U_rho.         (SF8)

This law is fixed for the entire chosen chain, not chosen separately
for each original. Every chain gives its own valid inequality, so one
can minimize the numerical left side over chains without identifying
their probability laws.

All pure powers 3,...,3^H are present and their APs are disjoint. Hence
the total non-pure root-tail measure, summing the two root copies, is

    B_H=2-sum_(e=2,...,H)3^(1-e)
       =(3+3^(1-H))/2.

Integrating SF8 and then enlarging to all mixed originals gives

    sum_(3^e m original, m>1)3^(1-e) gamma_P(m)>=B_H. (SF9)

It is a necessary condition on the actual original palette. A violation
would give a root-tail with chain price below one and the whole-cover
descent certified by 376. This argument makes no claim that the
new law is original Haar.

## 4. Three active mixed labels have only one possible form

Use the full consecutive prime chain above 3. Every base in SF7 is
at least three, so SF8 forces at least three active mixed originals
at every non-pure root-tail. If there are exactly three, each price
must be 1/3. Thus each cofactor is squarefree and uses only primes
whose preceding support prime differs by two. In particular 11 is
excluded by its base 11-7+1=5.

Suppose any of the three cofactors had a prime factor p>=13. Choose
it as representative for that cofactor and one prime factor from
each of the other two. Form the chain of their distinct representatives.
Each cofactor's gamma is at most its assigned representative price.
If all three representatives are distinct, their even successive gaps
from 3 are at least two and sum to at least ten. Convexity of 1/(g+1)
on g>=2 bounds the reciprocal sum by

    1/3+1/3+1/7=17/21<1.

For two distinct representatives the multiplicities are two and one;
the same endpoint bound is 2/3+1/9=7/9. For one representative it is
at most 3/11. Each contradicts SF8. Consequently every cofactor is
one of 5,7,35.

Their full cofactor APs project to full rows, full columns or singleton
cells in the 5-by-7 grid, and the projected actual residual is contained
in their union. If 7 occurs, 376 requires this union to
meet every three-row by five-column rectangle. Such a union can do
so only if it is three distinct full rows or three distinct full
columns. To prove this, let r,c be the numbers of distinct full rows
and columns. If r,c<=2, delete them first. There are at most
3-r-c singleton cells left, while the remaining row/column deletion
budgets sum to (2-r)+(2-c). Assign each such cell one of these
available deletion slots, and extend to exactly two deleted rows and
two deleted columns. The remaining rectangle misses all three sets.
Repeated rows, columns or cells cannot improve their union.

Three columns would put the entire 7-projection of R_3 in at most
three roots, contradicting the one-coordinate lower bound of five
from 375. Thus all three cofactors are 5 and their specified 5-residues
are distinct. If 7 never
occurs among the cofactors, this conclusion is immediate from the
first-5 projection lower bound of three. The only possible labels are

    3^(e_1)*5, 3^(e_2)*5, 3^(e_3)*5,               (SF10)

with distinct e_i and distinct first-5 residues. Numerical-modulus
distinctness forces the exponents to differ, so H>=3.

## 5. A nonvanishing tail-incidence requirement

Define the actual mixed tail incidence

    I_3=sum_(3^e m original, m>1)3^(1-e).

It equals the integral of the number N_rho(t) of active mixed originals
over both root-tail copies, because each original trace meets R_3.
Outside the pure prefixes, N is at least four except where SF10 holds.

There is at most one numerical label 3^e*5 for each exponent e, thus
at most one corresponding tail prefix globally at each depth e-1.
A tail with at least three such selected prefixes has a unique third
selected ancestor. These third-ancestor cylinders are disjoint and
their depths are at least two. Their total measure is at most

    c_H=sum_(j=2,...,H-1)3^(-j),                   (SF11)

where the empty sum is zero. It bounds the three-label exceptional
set, even if some other tails also belong to three selected prefixes.
Therefore

    I_3>=4B_H-c_H
       =8                               if H=1,
       =35/6+(5/2)*3^(1-H)              if H>=2.   (SF12)

This is a bound on tail incidence, not original AP Haar mass:
3^(1-e)=3m/d for d=3^e m. Large cofactors can have substantial tail
incidence and small original Haar mass. The latter still needs a
separate joint estimate.

## 6. The actual first-5 dichotomy strengthens different sides

Pure 3-powers alone cannot cover, so the initial-segment support
contains 5. The original A_5=0 excludes zero from the first-5
projection of R_3, while 375 supplies at least three roots. Hence
its size is exactly three or four.

If it has four roots, SF10 cannot cover R_3 at any non-pure root-tail.
There is no three-label exception, and

    I_3>=4B_H=6+2*3^(1-H).                         (SF13)

If it has three roots, apply sections 1--2 with q=3, p_1=5 and k=1.
For any selected chain beginning with 5, let c(m) use its remaining
prime gaps as in SF6. One law on actual R_3 now has AP price

    gamma_sat(m)=c(m)                         if 5 does not divide m,
    gamma_sat(m)=(1/3) min(3^(1-v_5(m)),c(m)) if 5 divides m. (SF14)

It is no larger than the old minimum-of-marginals price. For example,
with chain 3<5<7, an AP containing one factor each of 5 and 7 has
price at most 1/9 instead of 1/3. This controls actual composite
queries through one constructed law. Repeating the same-law union
argument gives the strengthened necessary condition

    sum_(3^e m original, m>1)3^(1-e) gamma_sat(m)>=B_H. (SF15)

Thus the two cases are exhaustive: the larger projection strengthens
the incidence bound, and the saturated projection permits stronger
joint prices. Neither side alone yet yields the required global
contradiction. The construction does not claim mutual independence
of unsaturated coordinates or preservation of original Haar.

## 7. Checks, reuse and scope

[The exact finite controls](../../frontier/cover-geometry/saturated_prefix_disintegration.py)
isolate all 27 leaves of a nonuniform ternary depth-three subtree in
the five-ary tree. They check all 18424 multisets of three grid boxes
against all 210 relevant rectangles: exactly the ten row triples and
35 column triples block every rectangle. They also check the rational
incidence formulas at H=1,...,8 and sixteen old/new price comparisons.
These controls test the ordinary arguments and do not instantiate an
unknown minimum odd cover or replace their unbounded proofs.

The full-chain obstruction and weighted LP lemma are reused from 376;
the exact minimum one-coordinate tree comes from 375. The original
trace/private-point fact is in 364, and the original minimum-cover
conventions are in 350. The search through the relevant 340,350,
354--355,360,364,366--372,375--376 interfaces found no bound with the
same mixed-tail-incidence statistic and quantifiers. The existing
cofactor-height matching results concern different source-weighted
quantities and are not replaced by SF12. A targeted prefix/fibre
search found no same conditional construction in that scope.

The chain-price rigidity and incidence argument were supplied through
the Nyx oracle and independently checked. The saturated-fibre
disintegration was separately derived and independently checked; the
same-source and all-height conditions are explicit above. No claim of
literature priority or new Lean certification is made. The unresolved
step is to make these lawful composite prices and/or original incidence
requirements contradict the full original covering budget.
