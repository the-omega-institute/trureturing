# A coherent root hypergraph supplies exact query maxima and actual deletion credit

For a coherent forbidden-root hypergraph, an exposing minimal edge determines
exactly which query maxima decrease when one all-nonspecial live cell is deleted.
A sixteen-original arithmetic instance retains a positive common-source
continuation through arbitrary29-ending classes and every finite prime tail
strictly above40000. This is a restricted phase class, not unrestricted odd
covering. The proof and finite arithmetic are ordinary mathematics, not Lean.
The inherited analytic input is [Report734 HM14](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md),
using its stated Rosser--Schoenfeld Theorem8 consequence; the arithmetic consumer
does not reprove that input.

## 1. General hypergraph statement and its complete-height meaning

Let P be a finite set of distinct primes. Choose 2<=K_p<=p-1 and root alphabets
A_p={1,...,K_p}. Let H be a finite hypergraph on P with no empty edge. Remove
every edge properly containing another edge; this leaves a clutter and does
not alter the allowed roots. Write Q=product P. Let U consist of root tuples
in product A_p for which no hyperedge is entirely at the special root1.
Extend U by Haar in every higher prime-adic digit, and let mu=Haar|U.
For an arbitrary nonnegative weight vector w define

    Z_H(w)=sum_(I containing no edge of H) product_(p not in I) w_p.

The source has root-cell count Z_H(K-1) and mass Z_H(K-1)/Q. For S subset P,
let M_S be the largest absolute mu-mass of a cylinder specifying the roots at
the coordinates of S. Then the exact maximum is

    Q M_S=Z_(H[P\S])(K-1).                              (G1)

Indeed, pinning every coordinate in S to a nonspecial root introduces no new
restriction on the free coordinates. Changing some pins to1 adds constraints
and cannot increase the number of completions. The nonspecial pinning attains
the displayed induced-hypergraph partition count. H[P\S] keeps exactly the
hyperedges entirely within P\S. This is an exact maximum, not
an independent-event estimate.

For a numerical query modulus d with positive exponent support S and exponents
e_p>=1, Haar continuation gives

    max_a mu(a mod d)=M_S product_(p in S) p^(1-e_p).

Consequently the complete first query budget, INCLUDING old cofactor1, is

    B_P(mu)=sum_(d P-smooth, including1) max_a mu(a mod d)
           =sum_S M_S product_(p in S) p/(p-1)
           =Z_H(K-1+c)/Q,      c_p=p/(p-1).             (G2)

To prove the last equality, expand each product in Z_H(K-1+c): choosing a c_p
term selects S disjoint from the independent set I; the remaining sum over I
is precisely Z_(H[P\S])(K-1). Nonnegative geometric convergence justifies
complete heights. No finite-height sample supplies this quantifier.

Singleton hyperedges are allowed in this abstract model. For an actual
dictionary that already includes0 mod p, use only mixed hyperedges of size
at least2: a further1 mod p would reuse the same numerical modulus. Distinct
mixed hyperedges give distinct squarefree moduli and coherent CRT phases.

The old cofactor1 is bookkeeping for actual pure new-prime powers, not an
original modulus1. It must be present in B_P when testing the threshold28
for the next prime29.

## 2. Exactly when deleting one actual live cell decreases a query maximum

Delete the entire root cylinder x*=(2,...,2), and set

    mu'=mu-Haar|[x* mod Q],      V2={p:K_p=2}.

For each root query S, its integer maximum drops by exactly one if and only if

    S subset V2, and every v in S has an edge E with E intersect S={v}.     (G3)

The empty set satisfies this condition and represents the one-cell mass loss.
Here is a complete proof, including possible competing maximizers.

* If some pinned coordinate v has K_v>2, change its root from2 to a different
  nonspecial root. This is a distinct maximizing projection fiber unaffected
  by deletion, so the maximum does not fall.
* Suppose all K_v=2 on S. If v has no edge E with E intersect S={v}, changing
  just its pin from2 to1 activates no new edge: any edge containing v either
  has another pinned root2 or fails the specified intersection condition.
  Thus an unaffected maximizing fiber again remains.
* Conversely, let a different pinning have a nonempty special-pin set T
  within S. Choose v in T and an edge E with E intersect S={v}. Put the free
  vertices E\{v} at1 and all other free vertices at2. This is a legal old
  completion: any old forbidden edge F would have to lie in E\{v}, making
  F a proper subset of E, contrary to the clutter assumption. But the changed
  pinning now makes E entirely special, so it excludes this completion.
  Every distinct pinning has strictly fewer completions. Pins outside the
  alphabet have zero completions. Hence the all2 fiber is the unique maximum.

All counts are integers. Removing one point from a unique maximum decreases
the maximum by exactly one, even if formerly submaximal fibers tie afterward.
If another maximum exists it remains untouched. This proves (G3), and hence

    Q(B_P(mu)-B_P(mu'))
      =sum_(S subset V2, every v has E intersect S={v})
         product_(p in S) p/(p-1).                     (G4)

For an ordinary graph this is exactly the condition that every pinned v has
a neighbor outside S. Singleton edges satisfy it through E={v}; empty edges
are excluded since they would make the old source empty. Minimalization is
essential: raw edges{0} and{0,1}, with K=(2,2) and S={1}, would incorrectly
make{0,1} witness a decrease. In fact the legal roots are(2,1),(2,2), and
after deleting(2,2) the maximum at S remains1. Removing the redundant edge
recovers the correct condition and zero drop.

This is a concrete evaluation of the existing phase-slack/intersection
deletion-credit identity. It is not a replacement for that identity in
arbitrary sources, nor does it say that current numerical maxima alone form
a state closed under future deletion.

## 3. Literal sixteen-original source and signs

Use

    P=(3,5,7,11,13,17,19,23), Q=111546435,
    K=(2,2,2,2,4,4,4,3).

The first fifteen actual originals are0 mod p for all p in P, together with

    1 mod33, 1 mod85, 1 mod133, 1 mod143,
    1 mod221, 1 mod323, 1 mod437.

They give the graph3--11--13--17--19--23, with extra edges5--17 and7--19.
Its3072-root incoming block has1482 surviving roots. The sixteenth original
is2 mod Q and removes exactly the live all2 cell, leaving1481 roots. The
producer reconstructs CRT residues and applies the literal numerical phases;
it does not define arithmetic survival by graph membership.

The exact budgets are

    B_P(mu)/m(mu)=1513740786341/54086123520 <28,
    Q(B_P(mu)-B_P(mu'))=351/20,
    B_P(mu')/m(mu')=1513100292773/54049628160 <28,
    B_P(mu)/m(mu')=1513740786341/54049628160 >28.

For this graph, eligible supports are exactly the subsets of{3,5,7,11}
which do not contain both3 and11. Their sum is

    (1+5/4)(1+7/6)(1+3/2+11/10)=351/20.

The surviving absolute slack is

    sigma=28m(mu')-B_P(mu')=289295707/4070927302041600.     (G5)

This deletion does NOT improve the normalized budget: it rises from
27.9875999207... to27.9946475911.... The exact credit is needed to retain a
positive sufficient certificate; a mass-only subtraction would lose it.
The absolute slack also decreases, by(28-351/20)/Q.

A phase-sensitive control changes only1 mod143 to67 mod143, whose11-root
is1 and13-root is2. This leaves the numerical labels and each individual
incoming-block event mass unchanged, but leaves1464 roots and gives

    B_P(mu_changed)/m(mu_changed)
       =1503075311141/53429207040 >28.

Its source mass differs from the coherent source. It is not an equal-mass
or equal-marginal-source witness and must not be described as one.

## 4. Fourth-moment envelope: every root contribution has a factor p

Write M'_S for the absolute root-cylinder maxima of mu'. For

    A4(p)=sum_(j>=1) ((j+1)^4-j^4)p^(-j)
         =15t+50t^2+60t^3+24t^4,       t=1/(p-1),

define

    K4=sum_S M'_S product_(p in S) [p A4(p)].            (G6)

The factor p is necessary: a depth-j root-cylinder mass is M'_S*p^(1-j),
not M'_S*p^(-j). Omitting p here would give an incorrect bound.

For any four complete finite P-query dictionaries with independently fixed
phases, expand their product into ordered numerical-modulus tuples. An
intersection is empty unless all CRT compatibility equations hold; otherwise
it is the single cylinder at their lcm. Bound its mass by the corresponding
root maximum and Haar suffix factor. Counting the four exponent tuples with
maximum j gives((j+1)^4-j^4). Summing gives(G6). Thus K4 controls all four
query products on the same unnormalized source. It is an upper envelope;
after deleting the all2 cell, this argument does not establish a common
attaining dictionary or equality for arbitrary phases.

Extend mu' by independent Haar at29. Delete every actual original divisible
by29 whose other prime factors are in P, with arbitrary phases and heights.
Distinct full numerical moduli permit at most one original per pair(d,j),
d P-smooth including1 and j>=1. The union bound loses at most B_P(mu')/28,
so the restricted source nu29 has

    m(nu29)>=sigma/28=289295707/113985964457164800.

Restriction can only decrease nonnegative query products. Haar at29 gives

    K29=K4(1+A4(29))
       =102509552036551597634646100370192341
         /8740445251530270887053885440000
       =11728.184215627265....                         (G7)

No normalization or full-support completion is required: a positive supported
submeasure suffices to certify an actual survivor.

## 5. Complete arbitrary-prime tail above40000

Apply Report734 HM7--HM15 to nu29 with order4, delta=2/5, r=25, B=40000,
and ell=9. Its conditional live kernel has loss and quartic propagation

    loss_p <= (5625/2048) K_before/(p-1)^4,
    K_after <= K_before[1+(5/3)A4(p)].

The polynomial bound

    1+(5/3)A4=1+25t+(250/3)t^2+100t^3+40t^4 <=(1+t)^25

holds coefficientwise. The analytic-tail hypotheses are B>=286, ell>=4,
3^ell<=B, and4ell>=25, all satisfied. Thus the total loss is bounded by
K29*tau, where

    tau=(5625/6144)*((2ell^2+1)/(2ell^2-1))^25
          *B/(B-1)^4 *sum_(j=0..25) 25!/((25-j)!(3ell)^j).

Exact rational arithmetic gives

    sigma/28-K29*tau > 1/1000000000.

The explicit positive distorted mass is approximately1.3047614e-9. It is
not a Haar density lower bound of the same size. If there are s tail primes,
the inherited kernel density cap gives the Haar bound
(3/5)^s/1000000000 if one needs a density conversion.

Consequently every finite family satisfying ALL these restrictions fails to
cover the integers:

1. Its old P-smooth originals contain the sixteen literals above; any other
   old original misses the retained mark U minus the all2 root cell.
2. All originals involving29 and no prime outside P union{29} have arbitrary
   heights and fixed phases; full numerical moduli remain pairwise distinct.
3. Every other prime appearing anywhere in the family is strictly above40000.

In particular, intermediate primes31 through40000 cannot occur silently in
tail cofactors. Tail originals may have arbitrary earlier cofactors, heights,
and phases, and any finite number of tail primes is allowed. Each original
is assigned once to its greatest tail prime, as in Report734. This is a
phase-restricted subclass theorem, not the unrestricted odd-covering result.

## 6. Independent checks and relation to existing results

The [consumer](../../../frontier/cover-geometry/refined-capped-source/graph_query_deletion.py) and retained [exact results](../../../frontier/cover-geometry/refined-capped-source/graph_query_deletion.json) check three actual root-source maxima dictionaries, each with
256 query supports and40500 block phases. It checks3072 CRT reconstructions,
all29 proper-divisor pairs among the sixteen originals, exact budgets and
slack,27 finite/exact-tail moment identities, all analytic range and rational
margin inequalities. Its generic controls independently test160 five-vertex
graph/root-alphabet configurations (empty graph, star, path, cycle, complete
graph; all K in{2,3}^5), with5120 query supports. Three malformed structure
controls are rejected. A further1024 raw hypergraph/root-size configurations
cover all128 hyperedge families on three vertices and all K in{2,3}^3, with
8192 support cases. These independently test source-preserving minimalization,
the induced partition maximum and the clutter criterion, including singleton
edges, redundant supersets and deletion to the zero source. An explicit
nonminimal-edge false-positive control and an empty-edge rejection are checked.
Normal and optimized Python both pass; no `assert`
statement can disappear under optimization.

Prior mathematical infrastructure remains prior infrastructure: Report411
retains the joint residue histogram; [Report571 JB7--JB9](../550-599/571-joint-residual-laws-retain-conditional-and-query-incidence.md) and [Report752 JC1--JC5](752-joint-deletion-credit-distinguishes-equal-marginal-sources.md)
give general deletion credit; [Report750](750-marked-boundaries-and-joint-deletion-updates.md) gives the joint update; [Report755](755-current-query-maxima-are-not-a-closed-continuation-boundary.md)
shows that current maxima need not close under continuation. [Reports648](../600-649/648-induced-pair-responses-release-all-square-pairs.md)/[652](../650-699/652-a-realizable-obstruction-to-the-fixed-fifteen-star-criterion.md)
already use induced-graph partition responses/envelopes. The graph calculation
above supplies exact attainment for this coherent source and the exposing-edge
criterion that evaluates the existing deletion identity. The graph criterion
is its size-two special case. The review/search
scope does not establish external novelty of these ordinary finite identities.

The remaining unrestricted bridge is substantial: an arbitrary old phase
layout need not supply this coherent mark, an admissible mass of equivalent
marks, or any known compensating query bound. None is supplied by the numeric
tail improvement.
