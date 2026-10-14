# Original BDR Proposition 3.4

## Abstract

The original numbered-path alignment gives both balances at the same fixed lag.

**Theorem 1.1 (From the original alignment to both balances).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced.originalBDRProposition3_4`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced.originalBDRProposition3_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is BDR, arXiv:2411.05598v1, Proposition 3.4, on the original data. Let A and B be essential square matrices over the natural numbers on Fin n and Fin k, let R and S be arbitrary rectangular matrices of sizes n by k and k by n, and fix m > 0. An edge from i to j is its actual number in Fin(A i j). A finite path of length d is an endpoint-indexed sequence of these numbered edges; no multiplicity is replaced by a Boolean adjacency relation.

EdgePair(X,Y,i,w) is the dependent sum over middle vertices j of Fin(X i j) times Fin(Y j w). The four supplied endpoint-preserving bijections are phiR: AR ≃ RB, phiS: BS ≃ SA, psiA: RS ≃ A-paths of length m, and psiB: SR ≃ B-paths of length m. These are chosen bijections, not merely equalities of matrix products. Every conclusion uses these very same four maps.

AlignedA is the following literal local identity. Given numbered a in A(i,j), r in R(j,z) and s in S(z,w), write phiR(i,z)(j,a,r)=(t,r1,b) and phiS(t,w)(z,b,s)=(u,s1,a1). Then appending a1 to psiA(i,u)(t,r1,s1) equals the path with first edge a followed by psiA(j,w)(z,r,s). AlignedB is the same assertion after interchanging A with B, R with S, phiR with phiS and psiA with psiB. In particular, its phiR input middle vertex is j.

The concatenation supplier is IncomingLiftAmbiguityCriterion.concatenate_paths, extracted from that owner’s existing proof. It constructs a length d+e path whose numbered word is the append of the two words, and whose incoming lift is the composition of their lifts. Its use here takes the identity vertex lift. This extraction contributes no new mathematical claim beyond the existing supplier.

The inverse to concatenation cuts a length d+e path after its first d edges and retains the middle vertex in a dependent sum. Induction on the actual path proves word_cut. Equality of numbered words with a fixed start and length recovers both the dependent endpoint and the path: at a cons node the first edge determines its target and its Fin edge number, then the tail induction applies. This proves word_endpoint_injective and split_word_injective, including zero-length paths and empty fibers. Thus concatenateEquiv has both inverse equations on the actual paths.

For arbitrary d, sweep phiR moves an R edge backwards through an A path alpha; sweep phiS then moves the S edge through the resulting B path. Write the whole dependent output as (t,r1,u,s1,gamma). The invariant is word(psiA(i,u)(t,r1,s1)) ++ word(gamma) = word(alpha) ++ word(psiA(j,w)(z,r,s)). The lag of psiA remains the original fixed m for every d.

The proof of whole_word_invariant inducts on the complete Sigma-valued path input and retains both intermediate vertices and every numbered edge. The empty path is immediate. In the cons case the induction hypothesis treats the tail, the original AlignedA identity handles the first edge, and word_appendPath plus associativity of list append joins the two equalities. The local hFR, hGS and hword facts only normalize the same sweep outputs; they introduce no shorter-lag hypothesis.

Encoding the double-sweep output applies the same psiA to its RS pair and concatenates that m-path with gamma. The invariant identifies this encoded path with alpha concatenated with psiA of the original RS pair. The latter has length d+m, so lengthCast transports it along d+m=m+d before the inverse encoding cuts at m. This proves composition_fixed_lag on complete numbered paths, not on counts, endpoints alone or a scalar summary.

At d=m the cast m+m=m+m is the identity. Cutting the concatenation after m edges recovers alpha itself, so decoding with the original psiA inverse gives BalancedA. Explicitly, if psiA(i,j) inverse of alpha is (t0,r0,s0), the double sweep outputs (t0,r0,j,s0,psiA(j,w)(z,r,s)). Repeating the same argument with A,B and R,S exchanged gives BalancedB using the original psiB and the same phiS and phiR. The public theorem returns both balances as a conjunction.

Essentiality of A and B and positivity of m remain in the public telescope to match Proposition 3.4; the implication proof does not use them. The result retains arbitrary R and S, fixed m, all original bijections, edge numbers, both balances and degenerate fibers. It asserts no stronger SSE chain, common chi, bilateral conjugacy, quantitative bound or completion of the surrounding SFT problem. This is a formal derivation of the cited proposition, without a mathematical novelty claim.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced.originalBDRProposition3_4`
- Dependency: [D5/S3/ConceptDynamics/Coding/CommonNilpotencyForgettingBound](CommonNilpotencyForgettingBound.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting](CompatibleResponseForgetting.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/IncomingLiftAmbiguityCriterion](IncomingLiftAmbiguityCriterion.md)
