[Index](../../marked_head_profile.md) · [Same-law forest certificates](../321-384/334-same-chain-overlap-and-future-risk-certificates.md) · [Exact three-prime minimum](../../problem-details/10-a-four-prime-head-and-a-restricted-noncoverage-theorem.md)

# Chordal overlap certificates and their exact finite limits

The original-label compatibility graph gives exact inclusion–exclusion, while a chordal subgraph gives a smaller, certified lower bound on survival. The omitted quantity is exactly the expected excess number of active connected components. On all nonunit divisors of 945, the best certificate using a chordal subgraph of the forced-coprime graph is 175/945. The best forced-coprime forest gives 141/945, and the repository's previously proved exact minimum is 191/945. Thus the chordal improvement is real but leaves a definite 16/945 gap even in this finite head.

These are ordinary mathematical deductions and finite exact calculations. The chordal sieve and its higher-order overlap setting are mature methods; no mathematical novelty or new Lean result is claimed. None of the statements proves unrestricted Erdős #7.

## 1. Exact original-label compatibility and deletion–contraction

Let C_i be the event x = a_i mod m_i, with one label for each original modulus, on the uniform space Z/L, where every m_i divides L. Put

    ij in G iff a_i = a_j mod gcd(m_i,m_j).

The generalized Chinese remainder theorem says that an intersection indexed by S is nonempty exactly when S is a clique of G. A nonempty such intersection has density 1/lcm(m_i : i in S). Consequently the exact survivor density is

    delta = sum_{S clique in G, including empty S}
              (-1)^|S| / lcm(m_i : i in S),                 (CG1)

with the empty denominator equal to 1.

For an induced vertex set A and positive integer d, define

    P(A,d) = sum_{S clique in G[A]}
                 (-1)^|S| / lcm(d, m_i : i in S).

Splitting cliques according to whether they contain v gives

    P(A,d) = P(A minus {v},d)
             - P((A minus {v}) intersect N_G(v), lcm(d,m_v)),
    P(empty,d) = 1/d.                                      (CG2)

This evaluates (CG1) exactly. At a state reached from a selected compatible clique B, with d=lcm(m_i:i in B) and every vertex of A compatible with every vertex of B, it has the physical meaning

    P(A,d) = mu((intersection_{i in B} C_i)
                  minus (union_{j in A} C_j)) >= 0.        (CG3)

Thus every reachable state has nonnegative value. The subtraction recurrence is not a Markov transition. An arbitrary state without the compatibility/history condition need not be nonnegative: for A={0 mod 3, 1 mod 9} and d=9, P(A,9)=-1/9. That state cannot arise from a compatible history of lcm 9.

The repository already proves #P-completeness of exact original survivor counting in binary input, even for zero phases, in [report 343, section 12](../321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md). In particular, (CG2) supplies an exact evaluator, not a polynomial-time algorithm or an unrestricted positivity theorem. When all phases are zero, G is complete; the lcm weights still retain the counting difficulty.

## 2. Chordal sieve with an exact remainder

The following statement holds for arbitrary finite events C_i on one probability space. Let H be a chordal graph on their labels, including isolated vertices, and write A(x)={i:x in C_i}. Let c_H(A) be the number of components of H[A], with c_H(empty)=0. Define

    B_H = 1 + sum_{nonempty cliques S of H}
                    (-1)^|S| mu(intersection_{i in S} C_i).

Then

    B_H <= delta,
    delta - B_H = E[c_H(A(x)) - 1_{A(x) nonempty}].         (CG4)

In particular, equality holds exactly when every nonempty active induced graph is connected almost surely.

Proof. Every induced subgraph of a chordal graph is chordal, and its clique Euler characteristic equals its number of components:

    sum_{nonempty cliques S of H[A]} (-1)^(|S|+1) = c_H(A).

One elementary proof removes a simplicial vertex v. If it has no remaining neighbor, its cliques contribute 1 and its component is removed. Otherwise its remaining neighbors form a nonempty clique, and the sum of all terms containing v is (1-1)^k=0. Removing v does not disconnect its component, because its neighbors already form a clique. Induction proves the identity, including the empty case. Integrating the identity gives B_H=1-E[c_H(A)], whereas delta=1-Pr(A nonempty), proving (CG4).

For original residue events, choose H as a spanning chordal subgraph of G. Every clique intersection in H then has its exact Haar mass 1/lcm, so

    B_H = 1 - sum_i 1/m_i
          + sum_{H-cliques S, |S|>=2} (-1)^|S|/lcm(m_S).
                                                               (CG5)

A forest is the special case with no cliques of size above two. The events and every intersection must belong to the same original family and the same probability law. Under a reweighted physical law, replace 1/lcm by the actual intersection mass. If exact masses are replaced by estimates, positive coefficients require lower estimates and negative coefficients require upper estimates.

Chordality is a sufficient condition, not a necessary condition for valid inclusion–exclusion certificates. More generally, the pointwise lower-bound argument only needs clique Euler characteristic at least 1 on each realizable nonempty active set. The complete actual compatibility graph G can itself be nonchordal: every realizable A is nevertheless a G-clique, so its Euler characteristic is 1 and the full formula (CG1) is exact.

## 3. Monotonicity and a cheap elimination formula

If H is a spanning subgraph of H' and both are chordal, then

    B_H' - B_H = E[c_H(A)-c_H'(A)] >= 0.                    (CG6)

Indeed, adding edges cannot increase the number of components. In particular, closing a length-two path i-k-j in a forest creates exactly one new triangle, and the improvement is

    mu(C_i intersect C_j) - mu(C_i intersect C_j intersect C_k)
    = mu((C_i intersect C_j) minus C_k) >= 0.

The triple subtraction is essential: the same physical overlap cannot be credited twice.

For a perfect elimination ordering v_1,...,v_n, let N_i^+ be the neighbors of v_i occurring later. They form a clique. Grouping every clique by its earliest vertex gives

    B_H = 1 - sum_i mu(C_{v_i} minus union_{j in N_i^+} C_j).  (CG7)

If every edge of H joins coprime moduli, {v_i} union N_i^+ has pairwise coprime moduli. The Chinese remainder theorem therefore reduces (CG7), for every choice of phases, to

    B_H = 1 - sum_i (1/m_{v_i})
                        product_{j in N_i^+}(1-1/m_j).     (CG8)

This evaluates a supplied chordal certificate using its ordering and edges, without enumerating all cliques. A rooted forest can be ordered with at most one later neighbor per vertex, recovering its pair-overlap correction.

An arbitrary cyclic graph cannot be substituted into (CG4). There is an original arithmetic counterexample: use the zero classes modulo 3,9,27,81 and let H be the four-cycle with edges 3--9, 9--27, 27--81, 81--3. The true survival is 54/81, since the 3-class contains all other classes. The unsupported cycle formula gives 55/81. At x=0 all four vertices are active, but the cycle has clique Euler characteristic 0 and one component. This rejects the unrestricted cycle formula; it does not reject other valid cyclic or higher-order certificates.

## 4. The exact 605 control

For the nonunit divisors 5,11,55,121,605,

    sum_i 1/m_i = 193/605.

The forced-coprime forest with edges 5--11 and 5--121 has correction 12/605, giving survival at least 424/605 for all phases. The assignment

    (m_i,a_i) = (5,0),(11,0),(55,1),(121,2),(605,3)

has exactly 424 surviving residues. Direct residue enumeration and (CG2), using 13 memoized states for the fixed order in the verifier, both return 424/605. Adding missing divisor labels can only decrease survival, so the same minimum 424 applies when arbitrary subsets of these five labels are allowed.

## 5. Exact limits of forced-coprime certificates at 945

Use all 15 nonunit divisors of 945. Their reciprocal sum is 65/63=975/945. The forced-coprime graph has a six-vertex core

    {3,9,27} union {5,7,35},

with every edge of K_(3,3), together with 5--7. There are six additional bridges,

    5--21, 5--63, 5--189, 7--15, 7--45, 7--135,

and three isolated vertices 105,315,945. Every bridge can be added to a chordal subgraph without destroying chordality and gives a strictly positive correction, so all six occur in an optimum. Only the ten core edges need to be searched.

Exact enumeration of their 2^10=1024 subsets gives 678 chordal core graphs. There is a unique optimal core: omit 9--35 and 27--35 and retain the other eight edges. Equivalently, take the three triangles {3,5,7}, {9,5,7}, {27,5,7} sharing edge 5--7, and attach 35 only to 3. Include all six bridges and three isolated vertices.

The shared-triangle part contributes 170/945 after its three triple subtractions. Edge 3--35 contributes 9/945 and the six bridges contribute 26/945. Thus

    max_{H chordal spanning subgraph of forced-coprime graph} B_H
      = 1 - 975/945 + 205/945
      = 175/945 = 5/27.                                 (CG9)

One perfect elimination order is

    9,15,21,27,35,3,45,63,105,135,7,5,189,315,945.

The best forest correction is 171/945=19/105, so the user-supplied forest is already optimal within the forced-coprime forest class. Its bound is 141/945. The chordal improvement over that class is therefore 34/945.

The previously established exact minimum for this divisor inventory is 191/945: problem-details/10, equation (CM9), gives 58*3^(H-2)+17 surviving residues for 3^H*35, H>=3. Hence the sharp gap between the forced-coprime chordal certificate class and true minimum at H=3 is 16/945. This is a limitation of the specified certificate class. It is not an upper bound on phase-dependent chordal certificates, arbitrary overlap certificates, or all methods based on relations.

The exact verifier checks every induced active subset of each of the 678 chordal cores, giving 43,392 Euler/component identity checks, and compares (CG5) against (CG8). These controls certify the finite arithmetic and graph optimization above; the general mathematical statements are proved directly.

## 6. An unavoidable blind range for coprime forests

Let q=min_i m_i>1 and S=sum_i 1/m_i. For any forest F whose edges join coprime moduli, choose q as the root of its component and an arbitrary root in every other component. Orient edges away from their roots. Since every parent modulus is at least q,

    W_F = sum_{parent--child} 1/(m_parent*m_child)
        <= (1/q) sum_{nonroot children} 1/m_child
        <= (S-1/q)/q.

Consequently every such forest certificate satisfies

    1-S+W_F <= (1-1/q)(1+1/q-S).                           (CG10)

If S>=1+1/q, no forced-coprime forest can certify strictly positive survival by this formula. This limitation holds irrespective of the phases. It does not constrain forests using actual noncoprime intersections, higher-order chordal corrections, or the actual survivor density.

For a concrete original family take all zero classes at odd moduli 3,5,...,29. Then 1 is an explicit survivor and

    S = 194460438112/145568097675 > 4/3.

The ceiling in (CG10) is -739282424/436704293025. Exact maximum-spanning-forest optimization gives the still smaller certificate value -5894572358/145568097675. Thus a genuine surviving family can lie beyond the positive range of every certificate in this forest class.

## 7. Existing interfaces and what is still missing

The graph here has one vertex per original event. It differs from the repository's forest of prime-coordinate constraints and from its prime-bag junction trees. The latter require full joint separator laws and assign each original label exactly once; replacing such laws by marginal overlap numbers has no justification. Existing ExactForestMessages and ForestConstraintEnergy results refer to those constraint structures, not to this event-overlap forest.

For a fixed CRT product, independent automorphisms of each rooted prime-digit tree preserve every divisor cylinder and its measure. A permutation preserving all fixed-modulus divisor partitions has this coordinatewise form: preserving the full p-coordinate partition makes that output coordinate depend only on its own input coordinate, and preserving every lower prefix imposes the rooted-tree condition. Child permutations may depend on earlier digits of that same prime. Arbitrary permutations of full layers or transformations depending on other prime coordinates need not preserve the original cylinders. If only a selected inventory is required to be preserved, additional symmetries can exist; the characterization above concerns all divisor partitions. Report 376's complete-prime-chain maps are a different, explicitly proved transport: full coordinate chains move to different primes with an injective numerical-label map and one common original witness.

To turn these certificates into an unrestricted E7 proof still requires a theorem ensuring a positive lower bound for every allowed original family, or a stronger common-law/overlap construction with sufficient quantitative gain. Exact counting, legal symmetries, and the choice of a chordal or higher-order graph do not supply that missing positivity theorem.

## 8. Mature sources

Klaus Dohmen, “Bonferroni-Type Inequalities via Chordal Graphs,” Combinatorics, Probability and Computing 11(4), 349–351 (2002), [DOI 10.1017/S0963548302005151](https://doi.org/10.1017/S0963548302005151). The publisher's abstract identifies the chordal graph sieve and its interpolation from Boole's inequality to exact inclusion–exclusion. Bibliographic data and the publisher abstract were verified; the publisher PDF endpoint returns the abstract/access page, so no theorem number or uninspected full-text detail is claimed here. Sections 2–3 contain the complete ordinary proof used in this note.

József Bukszár, “Hypermultitrees and Sharp Bonferroni Inequalities,” Mathematical Inequalities & Applications 6(4), 727–743 (2003), DOI 10.7153/mia-06-66, https://files.ele-math.com/articles/mia-06-66.pdf. Definitions 1–4 and Theorem 5 (pp. 727–729) give the higher-order multitree upper bound for a union; Theorem 14 (pp. 736–737) gives a monotone extension to the next order. The full primary text was checked. General multitrees use recursively selected parent sets and hyperedges; they are not identical to clique complexes of chordal graphs. Theorem 5's proof is ordered union disjointization followed by inclusion–exclusion, retaining the higher intersections that prevent duplicate overlap credit. This paper is already cited by repository report 334.

## Reusable finite evaluator

The [exact evaluator and graph controls](../../frontier/cover-geometry/chordal_overlap_certificates.py) implement the original-label clique DP, perfect-elimination and clique evaluations, maximum coprime forests, and the complete finite core comparison above. The controls use explicit exceptions and remain active with Python optimization enabled. Run with `python3 -I -S -B -O` followed by the script path; output uses exact rational values. The file is importable without running its controls.
