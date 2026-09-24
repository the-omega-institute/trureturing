# An actual sharp finite nine-cell interface for 3p and 9p blocks

The union of selected original classes with numerical labels3p and9p, p in Q={5,7,11,13,17,19}, has an exact nine-cell response under the complete actual pure-product law. Retaining their common ternary parents, their selected outside roots, and all deeper pure ternary deletions gives a computable upper envelope. For every fixed admissible low-pure mask and ternary incidence pattern, the saturated envelope is the SUPREMUM of actual finite irredundant families. Thus the unrestricted-height optimization for this block reduces exactly to a finite incidence problem. This does not optimize that finite problem or resolve arbitrary mixed cores.

## Scope, source law, and reused results

Let P={3,5,7,11,13,17,19}. Start with a finite actual irredundant core M0, globally fixed original phases, its complete pure-coordinate survivors S_p, and the one product probability

    rho0=product_(p in P) H_p(.|S_p).

Here H_p is Haar probability, every actual pure exponent is included, and all original mixed classes remain part of the full family. Select a block whose occupied numerical labels are3p for p in I and9p for p in K, with I,K subsets of Q. Upper bounds below concern this selected block under rho0. They do not condition separately on selected mixed survivors.

The basic ingredients are reused. [Report382](382-prime-star-overlaps-and-no-prime-excess.md), PS4--PS6, computes shared-root product unions under prime-only conditioning. [Chapter10](../../problem-details/10-a-four-prime-head-and-a-restricted-noncoverage-theorem.md), P12, retains modulo-nine pure deficits and parent-relative ADDITIONAL second-level deletion for one outside prime, including arbitrary pure ternary heights. [Report535](535-mixed-chain-moments-retain-shared-prime-correlations.md), MC1, proves disjointness of occupied comparable numerical cylinders in an irredundant core and explains why changing cofactors can invalidate a projected disjointness claim. [Report539](539-a-weighted-mixed-inventory-certifies-one-entropy-law.md) and [report541](541-shared-ternary-roots-certify-sixteen-mixed-heads.md) supply the complete pure-product source and the actual-loss budget consumer. [Chapter15](../../problem-details/15-exact-tensorization-for-two-fixed-depth-two-tree-shapes.md)'s depth-two Gamma tensorization has different hypotheses and a different task; it does not supply this block-union extremum.

The contribution here is the actual extremal construction and its precise finite block interface, including a counterexample to discarding the parent incidence. The conditional-product identity and pure-deficit simplex are not claimed as new general theory. These are ordinary deductions and constructions, not new Lean results or a claim of literature priority.

## The existing six-star ceiling is already an actual supremum

For p in Q set

    c_p=(p-1)/[p(p-2)],
    u(A)=1-product_(p in A)(1-c_p),
    C(J)=max_(A subset J)[(2/3)u(A)+(1/3)u(J without A)].

[Report541](541-shared-ternary-roots-certify-sixteen-mixed-heads.md) proves that the union of the selected originals3p, p in J, has rho0 mass at most C(J). The constant cannot be uniformly reduced within that block's stated setting.

Choose one maximizing subset A once. For each finite H>=1, take the pure originals

    p^(e-1) mod p^e, p in P, e=1,...,H.

For each selected3p original choose outside root2 modulo p and ternary root2 if p in A, otherwise ternary root0. All original mixed phases are fixed by CRT once, independently of H. The pure cylinders are disjoint: their first nonzero p-adic digits appear in different positions.

Write w_(p,H)=1-sum_(e=1 to H)p^(-e). Outside root2 has probability1/[p*w_(p,H)] tending to c_p. Ternary root2 has probability1/[3*w_(3,H)] tending to2/3; root0 has probability

    [1/3-sum_(e=2 to H)3^(-e)]/w_(3,H) ->1/3.

Root1 is excluded. The exact shared-root union therefore tends to C(J).

Every finite family is irredundant. A pure original's private point has only its own p coordinate equal to p^(e-1), all other coordinates zero. A star original's private point has its specified ternary coordinate0 or2, its own outside coordinate2, and all other outside coordinates zero. Take these as complete coordinates modulo p^H; the literal values0 and2 avoid every pure comb. CRT realizes the private points. This proves

    sup_(finite actual irredundant families) rho0(union_(p in J)C_(3p))=C(J).   (NB1)

The limit identifies a supremum using finite families; no infinite original family is substituted into a finite theorem. It does not establish sharpness of541's complete sixteen-label estimate, whose other mixed labels and tail were separately bounded. A further uniform improvement must retain additional information, such as the9p parent/child relations.

## Exact response on nine shared cells

For j in Z/9 put t_j=rho3([j]_9). Define the SET of outside roots active at that cell by

    E_p(j)={a_(3p) mod p : p in I and j mod3=a_(3p) mod3}
           union
           {a_(9p) mod p : p in K and j=a_(9p) mod9}.

Let theta_(p,b)=rho_p([b]_p), h_p(j)=sum_(b in E_p(j))theta_(p,b), and

    g_j=1-product_(p in Q)(1-h_p(j)).

Then the selected block B has the EXACT probability

    rho0(B)=sum_(j mod9)t_j*g_j.                                      (NB2)

Partition by the same ternary cell, first unite the selected roots on each outside p coordinate, and then multiply the independent avoidance events over distinct outside primes. The product is not over individual originals sharing p.

If both3p and9p are occupied, irredundancy and3p|9p force their original cylinders to be disjoint. Consequently, when their ternary placements overlap, their p-root phases must be different. On that cell h_p is the SUM of those two root probabilities, not1-(1-x_p)(1-y_p). When their ternary placements do not overlap, the two outside roots never activate together. Keeping E_p as a set also makes NB2 valid without an irredundancy assumption.

Thus the exact boundary consists of the actual nine-cell probability vector, at most two selected root masses per outside prime, the selected root identities, and each original's literal ternary root or child. Complete pure heights enter those probabilities; no full residue-period enumeration is needed to evaluate the formula.

## All pure ternary heights fit one retained deficit simplex

Delete the forbidden ternary root if the pure original3 is present, and the forbidden modulo-nine cell if the pure original9 is present. In an irredundant core these two exclusions are disjoint. Let J be the remaining cells and write

    N=|J|=9-3*epsilon3-epsilon9 in {9,8,6,5}.

Every pure3^e original at depth e>=3 lies in a cell of J, and these pure originals are disjoint. Define

    delta_j=9*sum_(occupied pure3^e, e>=3, a_(3^e)=j mod9)3^(-e),
    delta=sum_(j in J)delta_j<=9*sum_(e>=3)3^(-e)=1/2.

All actual pure ternary heights occur in these finite sums. The complete pure-conditioned source has exactly

    t_j=(1-delta_j)/(N-delta) for j in J,
    t_j=0 outside J.                                                (NB3)

Every allowed cell remains positive. For fixed nonnegative cell coefficients v_j, set S=sum_(j in J)v_j and m=min_(j in J)v_j. Then

    sum_j t_j*v_j
      <=(S-delta*m)/(N-delta)
      <=(S-m/2)/(N-1/2).                                            (NB4)

The first inequality uses sum delta_j*v_j>=delta*m. It is the exact optimum over the relaxed deficit simplex with this fixed total. The second quotient increases with delta, since its derivative is(S-N*m)/(N-delta)^2>=0. If the actual delta or the complete delta_j are available, retain them for the corresponding sharper bound. Chapter10 P12 already uses the five-cell version of this pure-deficit accounting; NB3 records all four low-pure cases.

## A cap interface and its fixed-incidence envelope

The complete pure-coordinate factor a_p=1/H_p(S_p) satisfies a_p<=(p-1)/(p-2), so each selected outside root has probability at most a_p/p<=c_p. For p>=5,2*c_p<1.

Let r_p be the fixed ternary root of3p, when p in I, and j_p the fixed ternary child of9p, when p in K. An admissible incidence has r_p outside a forbidden pure3 root and j_p in J. Define the simultaneous cell multiplicity

    n_(p,j)=1_(p in I and j mod3=r_p)+1_(p in K and j=j_p),
    v_j=1-product_(p in Q)(1-c_p*n_(p,j)).

For an actual irredundant core n_(p,j) equals|E_p(j)| whenever both events activate, because their outside roots then differ. Thus NB2 and monotonicity give

    rho0(B)<=sum_j t_j*v_j
      <=Phi_J(v):=[sum_(j in J)v_j-(1/2)min_(j in J)v_j]/(N-1/2).     (NB5)

One can use the smaller actual caps a_p/p in the first inequality, without changing any actual phases. That fixed finite-parameter variant is only an upper bound here. The sharpness theorem below applies specifically to the SATURATED constants c_p; it varies the finite pure layouts and does not hold the actual factors a_p fixed while taking their extremal limit.

A coarser bound uses just t_j<=2/9 and sum t_j=1. If the nine coefficients, including zeros on forbidden cells, are sorted v[1]>=...>=v[9], the capped-simplex maximum is

    [2*sum_(i=1 to4)v[i]+v[5]]/9.                                   (NB6)

It fills four cells with mass2/9 and the fifth with1/9. Every profile used in NB4 belongs to this capped simplex, so the retained-mask bound NB5 is never worse. Neither argument permits choosing a different incidence pattern independently for each cell.

## The fixed-incidence envelope is attained as an actual supremum

Fix an admissible low-pure mask J and the ternary incidences r_p,j_p. Fix the saturated coefficients v_j above and choose one minimizing cell j* in J. Consider all finite families whose low-pure labels/phases and selected ternary incidences have these fixed values, allowing their outside phases and higher pure layouts to be chosen. The envelope in NB5 is their exact supremum. Equality already holds as a supremum among families with NO mixed originals other than the selected block.

For every H>=3 retain the chosen pure3 and pure9 originals, when specified by the mask. Include every higher pure ternary original through depth H with phase

    j*+3^(e-1) mod3^e, e=3,...,H.

They all lie inside the good cell j*, and are disjoint by the position of their first nonzero digit above the first two ternary digits. Their total deficit is

    delta_H=9*sum_(e=3 to H)3^(-e)->1/2.

The literal residue j* itself avoids every such higher original.

For each outside prime q in Q, include the pure comb

    q^(e-1) mod q^e, e=1,...,H.

Give every selected3q original outside root2, and every selected9q original outside root3, retaining its prescribed ternary incidence. These CRT phases are fixed once and do not depend on H. Both outside roots are untouched by the comb and have the SAME probability

    x_(q,H)=1/[q*(1-sum_(e=1 to H)q^(-e))] ->c_q.

Let v_(j,H)=1-product_q(1-x_(q,H)*n_(q,j)). The complete actual pure-product law then gives the exact block union

    [sum_(j in J)v_(j,H)-delta_H*v_(j*,H)]/(N-delta_H)
       ->Phi_J(v).                                                (NB7)

All these finite families are irredundant. For a selected3q class, choose any allowed literal cell j in its prescribed parent root, set the outside q coordinate to2, and all other outside coordinates to zero. For a selected9q class, choose its prescribed literal cell j_q and outside q coordinate3. A literal cell j in{0,...,8} has no higher ternary digits and avoids every new deep pure ternary original. The two numerical labels on the same q use different outside roots; every other mixed label misses because its outside coordinate is zero.

For a pure outside-q original, take q coordinate q^(e-1), any allowed literal ternary cell, and all other outside coordinates zero. Its outside root is1 or0, avoiding both selected mixed roots2 and3; pure-comb disjointness separates all other pure originals. For each pure ternary original, take its own ternary phase and all outside coordinates zero. The disjoint pure ternary layout and zero outside coordinates exclude every competing original. CRT realizes every private point at the full finite heights.

This proves actual sharpness, including missing pure3, missing pure9, and either or both mixed slots absent at any outside prime. It is a statement about fixed TERNARY incidence and low-pure mask with freely constructed outside phases and pure layouts. It does not claim equality for arbitrary preassigned complete original phases, nor compatibility with a separately prescribed collection of other mixed originals. The upper bound NB5 continues to hold when those further originals are present.

## A finite simultaneous recurrence

For a given mask and incidence pattern, start with the avoidance vector z=(1,...,1) on J. Adding the selected slots associated with one outside prime p updates all cells together:

    z'_j=z_j*(1-c_p*n_(p,j)).                                     (NB8)

After the outside primes are processed, v_j=1-z_j. Known fixed incidences therefore take at most nine scalar multiplications per outside prime.

For a phase-independent block bound with fixed I,K, retain a finite SET of such full vectors. A local transition chooses one root for a3p slot and one child for a9p slot when present. The root affects all its children at once; the child affects one position. No forbidden root or child is allowed. Evaluate Phi_J after the last prime, then maximize over the finite joint incidence choices and, if necessary, over the four low-pure mask types. By NB5 and NB7 this finite maximum equals the supremum over actual finite irredundant families for this selected block. Tree symmetries permit canonical mask representatives while transporting all incidences together.

Only within the SAME allowed-cell mask J and the SAME remaining-prime stage, with identical remaining transitions, coordinatewise dominance permits discarding z' when z<=z': the latter avoidance vector cannot give a larger union under any admissible common ternary law. Incomparable vectors must be kept. Every outside prime is processed exactly once, with BOTH of its selected slots included in that update. The avoidance vector alone does not justify a later independent multiplication by another block sharing an already processed outside prime; such an extension needs its joint coordinate boundary. This is an exact finite reduction; no general polynomial bound on the number of retained vectors or economical evaluation of its maximum is proved here. No27^6 phase enumeration or full numerical-label scan is required for the reduction, and none was run for this result.

## An actual paired counterexample to separate depth marginals

Two complete finite families have the same four pure originals

    1 mod3, 3 mod9, 1 mod5, 1 mod7,

and the same mixed original E=12 mod15. Family A additionally has F_A=9 mod63; family B instead has F_B=2 mod63. All phases are globally fixed in each family and there are no further originals.

Under their COMMON pure-product law rho0, the ternary coordinate is uniform on{0,2,5,6,8} modulo9, the5-coordinate is uniform outside root1, and likewise at7. The complete nine-cell source vector and the root vector(2/5,0,3/5) agree between the two families. Also

    rho0(E)=1/10,
    rho0(F_A)=rho0(F_B)=1/30.

Each depth has only one mixed event, so the entire separate within-layer indicator distributions coincide. The outside-root phases also agree. However F_A uses ternary child0 below E's parent0, while F_B uses child2 below the other parent. Hence

    rho0(E intersect F_A)=1/120,
    rho0(E intersect F_B)=0,
    rho0(E union F_A)=1/8,
    rho0(E union F_B)=2/15.                                       (NB9)

The additional second-layer deletion is1/40 versus1/30. Their complete survivors and final conditioned laws are different; sameness is asserted only for rho0 and the specified marginal observations.

Both six-class families are irredundant. The following private integers, with CRT coordinates modulo(9,5,7), each hit only the indicated original:

| Original | Private integer | CRT coordinates |
| --- | ---: | --- |
| 1 mod3 | 280 | (1,0,0) |
| 3 mod9 | 210 | (3,0,0) |
| 1 mod5 | 126 | (0,1,0) |
| 1 mod7 | 225 | (0,0,1) |
| 12 mod15 | 252 | (0,2,0) |
| 9 mod63, family A | 135 | (0,0,2) |
| 2 mod63, family B | 65 | (2,0,2) |

The all-zero point survives both families. If exact support on all seven reference primes is required, append identical pure originals1 mod11,1 mod13,1 mod17,1 mod19. Extend the old private points by zeros; a new pure original's private point has only its own coordinate equal to one. The added independent conditioning changes none of NB9.

This counterexample refutes sufficiency of the pure source profile together with separate depth marginals. It does not refute a boundary retaining the labelled parent/child positions. Chapter10 P12 already retains precisely such parent-relative additional deletion; the finite pair makes the omitted relation explicit rather than asserting a new general need for joint probabilities.

## Returning to the complete survivor problem

The block response is a bound on ACTUAL deletion under one rho0. Valid bounds for every other occupied mixed original, including all deeper originals, must still be added before invoking541's actual-loss bridge on the full survivor U. The actual numerical capacity v and actual union loss l remain distinct: an improvement to a saturated block envelope must not be subtracted from an unrelated actual v.

NB1 locates the sharp boundary of the single-depth method. NB5--NB8 reduce the selected two-depth block to a sharp finite shared-incidence problem, and NB9 certifies that deleting the parent relation loses information. Computing an economical optimum for general selected two-depth inventories, combining additional mixed blocks that share outside prime coordinates, and closing the unrestricted mixed-core budget remain unresolved here. No improved shallow-label threshold is claimed.

## Verification scope

The [fixed counterexample consumer](../../frontier/cover-geometry/two_depth_boundary_counterexample.py) and [result](../../frontier/cover-geometry/two_depth_boundary_counterexample.json) verify the paired actual families, their private points, common pure-source profile and differing joint unions. The single fixed-fixture run completed35 exact checks with exit0. The arbitrary-height supremum constructions and nine-cell reduction are supported by the general proofs above, not by sampled finite instances. No Lean build, old producer rerun, original-family search or numerical-label inventory scan was performed for these results.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_depth_boundary_counterexample.py
```
