# The global ZZ gate-time upper bound

## Abstract

Every real symmetric zero-diagonal coupling matrix admits a nonnegative sign schedule within the parity-dependent gate-time bound.

**Definition 1.1 (Sign vectors with a fixed final sign).**

$$\forall (n: \mathbb{N}), ((\operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.SignVec}\left(n\right): \operatorname{Type}) = \operatorname{Subtype}\left(\lambda (s: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})) \mapsto (\forall (i: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin.val}\left(i\right) + (1: \mathbb{N}) = n) \to (s\left(i\right) = \operatorname{false})))\right))$$

*Formalization.* `D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.SignVec` (`✓ std3`).

*Citation.* Pascal Baßler; Markus Heinrich; Martin Kliesch (2024). *Time-optimal multi-qubit gates: Complexity, efficient heuristic and gate-time bounds*. DOI: [10.22331/q-2024-03-13-1279](https://doi.org/10.22331/q-2024-03-13-1279). URL: <https://arxiv.org/abs/2307.11160v2>.

*Commentary.*

A sign vector is a Boolean function on Fin n whose final coordinate is false. The Boolean b represents the real sign (-1) to the power Bool.toNat(b), so false represents plus one. The condition Fin.val(i) + 1 = n identifies the final coordinate without requiring n to be positive. This encodes the source's convention that the final sign is plus one (J_shaping.tex, lines 355-362); at n = 0 the condition is vacuous.

**Definition 1.2 (A nonnegative sign schedule).**

$$\forall (n: \mathbb{N}), (\forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), (\forall (lam: (\operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.SignVec}\left(n\right)) \to (\mathbb{R})), ((\operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.IsFeasible}\left(M, lam\right): \operatorname{Prop}) = \left((\forall (m: \operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.SignVec}\left(n\right)), ((0: \mathbb{R}) \le lam\left(m\right))) \land (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(n\right)), ((i < j) \to (M\left(i, j\right) = \sum_{(m: \operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.SignVec}\left(n\right))} ((lam\left(m\right)) \cdot ((((-(1: \mathbb{R}))^{\operatorname{Bool.toNat}\left(\operatorname{Subtype.val}\left(m\right)\left(i\right)\right)}) \cdot ((-(1: \mathbb{R}))^{\operatorname{Bool.toNat}\left(\operatorname{Subtype.val}\left(m\right)\left(j\right)\right)}))))))))\right))))$$

*Formalization.* `D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.IsFeasible` (`✓ std3`).

*Citation.* Pascal Baßler; Markus Heinrich; Martin Kliesch (2024). *Time-optimal multi-qubit gates: Complexity, efficient heuristic and gate-time bounds*. DOI: [10.22331/q-2024-03-13-1279](https://doi.org/10.22331/q-2024-03-13-1279). URL: <https://arxiv.org/abs/2307.11160v2>.

*Commentary.*

The real weights lam are nonnegative, and their weighted sign products reproduce every strictly upper triangular entry of M. Subtype.val explicitly extracts the Boolean function from each sign vector. This is feasibility for the source's linear program (J_shaping.tex, lines 265-288). The predicate itself imposes no condition on the diagonal or lower triangular entries of M.

**Definition 1.3 (The largest absolute upper triangular entry).**

$$\forall (n: \mathbb{N}), (\forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), ((\operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.offDiagSup}\left(M\right): \mathbb{R}) = \max_{(p: \operatorname{Option}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right)\right))} (\operatorname{Option.elim}\left(p, (0: \mathbb{R}), \lambda (e: \operatorname{Prod}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right)) \mapsto (\operatorname{ite}\left(\operatorname{Prod.fst}\left(e\right) < \operatorname{Prod.snd}\left(e\right), \left|M\left(\operatorname{Prod.fst}\left(e\right), \operatorname{Prod.snd}\left(e\right)\right)\right|, (0: \mathbb{R})\right))\right))))$$

*Formalization.* `D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.offDiagSup` (`✓ std3`).

*Citation.* Pascal Baßler; Markus Heinrich; Martin Kliesch (2024). *Time-optimal multi-qubit gates: Complexity, efficient heuristic and gate-time bounds*. DOI: [10.22331/q-2024-03-13-1279](https://doi.org/10.22331/q-2024-03-13-1279). URL: <https://arxiv.org/abs/2307.11160v2>.

*Commentary.*

Take the finite maximum over optional ordered pairs of indices. None contributes zero; a pair contributes the absolute entry when its first index is smaller, and zero otherwise. The extra zero makes this maximum defined and nonnegative even when there is no such pair. For a symmetric matrix this is the source's infinity norm of the vectorized off-diagonal entries (J_shaping.tex, lines 278 and 448).

**Definition 1.4 (The parity-dependent number of rounds).**

$$\forall (n: \mathbb{N}), ((\operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.gateBound}\left(n\right): \mathbb{R}) = (\operatorname{Nat.cast}\left((\operatorname{ite}\left(\operatorname{Even}\left(n\right), (n - (1: \mathbb{N})), n\right): \mathbb{N})\right): \mathbb{R}))$$

*Formalization.* `D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.gateBound` (`✓ std3`).

*Citation.* Pascal Baßler; Markus Heinrich; Martin Kliesch (2024). *Time-optimal multi-qubit gates: Complexity, efficient heuristic and gate-time bounds*. DOI: [10.22331/q-2024-03-13-1279](https://doi.org/10.22331/q-2024-03-13-1279). URL: <https://arxiv.org/abs/2307.11160v2>.

*Commentary.*

The multiplier is n minus one when n is even, and n when n is odd, as in the source's conjecture (J_shaping.tex, lines 919-927). Subtraction occurs in the natural numbers before Nat.cast includes the result in the reals. Thus the definition also gives zero at n = 0.

**Definition 1.5 (The upper bound for every coupling matrix).**

$$(\operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.claim}: \operatorname{Prop}) = (\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \to (\forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), ((\operatorname{Matrix.IsSymm}\left(M\right)) \to ((\forall (i: \operatorname{Fin}\left(n\right)), (M\left(i, i\right) = (0: \mathbb{R}))) \to (\exists (lam: (\operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.SignVec}\left(n\right)) \to (\mathbb{R})), ((\operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.IsFeasible}\left(M, lam\right)) \land (\sum_{(m: \operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.SignVec}\left(n\right))} (lam\left(m\right)) \le (\operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.gateBound}\left(n\right)) \cdot (\operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.offDiagSup}\left(M\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pascal Baßler; Markus Heinrich; Martin Kliesch (2024). *Time-optimal multi-qubit gates: Complexity, efficient heuristic and gate-time bounds*. DOI: [10.22331/q-2024-03-13-1279](https://doi.org/10.22331/q-2024-03-13-1279). URL: <https://arxiv.org/abs/2307.11160v2>.

*Commentary.*

For every natural n at least two and every real symmetric n by n matrix M with zero diagonal, there is a feasible nonnegative schedule whose total weight is at most gateBound(n) times offDiagSup(M). This states the upper-bound part of the source's conjecture for every M (J_shaping.tex, lines 240 and 919-927). Tightness is the source's Theorem prop:worst_case_sol (lines 1121-1130), which is cited rather than re-proved.

**Theorem 1.6 (A schedule from round-robin matchings).**

$$\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \to (\forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), ((\operatorname{Matrix.IsSymm}\left(M\right)) \to ((\forall (i: \operatorname{Fin}\left(n\right)), (M\left(i, i\right) = (0: \mathbb{R}))) \to (\exists (lam: (\operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.SignVec}\left(n\right)) \to (\mathbb{R})), ((\operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.IsFeasible}\left(M, lam\right)) \land (\sum_{(m: \operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.SignVec}\left(n\right))} (lam\left(m\right)) \le (\operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.gateBound}\left(n\right)) \cdot (\operatorname{D5.S3.Quantum.Optimization.GlobalZZGateTimeBound.offDiagSup}\left(M\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/bassler-heinrich-kliesch-2024-global-zz-gate-time-bound` (proved) by `D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bassler-heinrich-kliesch-2024-global-zz-gate-time-bound","declaration_gid":"D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pascal Baßler; Markus Heinrich; Martin Kliesch (2024). *Time-optimal multi-qubit gates: Complexity, efficient heuristic and gate-time bounds*. DOI: [10.22331/q-2024-03-13-1279](https://doi.org/10.22331/q-2024-03-13-1279). URL: <https://arxiv.org/abs/2307.11160v2>.

*Commentary.*

First partition all pairs i < j into K matchings, with K = n - 1 for even n and K = n for odd n. For even n identify the vertices with an extra point and ZMod(n - 1), and label the rounds by ZMod(n - 1). Color a pair of finite vertices x,y by x + y, and a pair consisting of the extra point and x by x + x. Addition is cancellative, and doubling is injective because n - 1 is odd. These facts show that distinct edges sharing a vertex have different colors. For odd n identify the vertices and rounds with ZMod n and color x,y by x + y; cancellation again gives the same property. In each case the color is symmetric in the endpoints. Orienting every edge by i < j therefore gives disjoint matching classes, and every such pair belongs to exactly one class.

For a Boolean function s write its ith real sign as (-1) to the power Bool.toNat(s(i)). Flipping the bits in a fixed set of vertices is an involution and negates exactly those signs. Consequently, any real function of s that changes sign under this involution has sum zero over all s.

For a matching R and real coefficients c(i,j), consider the product over its edges of 1 + c(i,j) times the ith and jth signs. Flipping whole edges and unmatched singleton vertices leaves this product unchanged. If i < j is absent from R, choose the block containing i: it is either its matching edge or the unmatched singleton. This block excludes j. Flipping it preserves the product but negates the product of the ith and jth signs, so the corresponding weighted pair sum is zero.

The sum of the product weights is 2 to the power n. To see this, induct on the matching. For the empty matching every weight is one. On inserting an edge, expand its factor: the extra term is its coefficient times the absent-pair sum for the smaller matching, which is zero. For a pair belonging to R, erase that edge and expand its factor in the weighted pair sum. The absent-pair term vanishes, and the square of each sign is one. The remaining term is c(i,j) times 2 to the power n.

When the absolute values of the coefficients are at most one, every product factor is nonnegative. Divide the weights by the positive real number 2 to the power n. The resulting probability law has pair moment c(i,j) on R and zero on every other pair i < j.

Next fold any nonnegative law onto SignVec n. At the final coordinate n - 1, inspect its Boolean value. If it is true, complement every bit; otherwise leave every bit unchanged. The final bit is then false, and complementing all bits preserves every pair of signs. Sum the original weights over each fiber of this map. The finite pushforward is nonnegative, preserves the total mass, and preserves every pair moment.

Set d = offDiagSup(M). The maximum contains zero, so d is nonnegative, and each absolute entry with i < j is at most d. If d = 0, all these entries vanish and the constant zero schedule is feasible with total weight zero. Otherwise d is positive, and the normalized coefficients c(i,j) = M(i,j)/d have absolute value at most one. For every matching class choose the probability law just constructed. Multiply their sum by d, then fold this nonnegative law onto SignVec n.

For each i < j, exactly one matching class contains the pair. Its contribution to the pair moment is M(i,j)/d, and all other classes contribute zero. Multiplication by d and preservation of pair moments under folding give precisely M(i,j), so the folded weights are feasible. Each class has mass one, hence their scaled sum has mass d times the real cast of K. Folding preserves this mass, which equals gateBound(n) times offDiagSup(M) and in particular satisfies the asserted inequality. The construction uses only the strictly upper triangular entries; symmetry and the zero diagonal specify the coupling matrices in the claim.

## References

- Truth anchor: `D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.IsFeasible`
- Truth anchor: `D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.SignVec`
- Truth anchor: `D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.claim`
- Truth anchor: `D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.gateBound`
- Truth anchor: `D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.offDiagSup`
- Truth anchor: `D5/S3/Quantum/Optimization/GlobalZZGateTimeBound.result`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/BipartiteMediatorPricing](../../ConceptDynamics/CausalMoments/BipartiteMediatorPricing.md)
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../../Entropy/Forgetting/CapacityMonotone.md)
- Dependency: [D5/S3/Observer/Linear/FiniteRealZeroFillRegister](../../Observer/Linear/FiniteRealZeroFillRegister.md)
