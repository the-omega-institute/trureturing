# Attractors of periodic prefix families

## Abstract

Coherent periodic prefix families admit endpoint attractors and full-block residual windows.

These generic suppliers use one coherent family of literal finite prefixes. The endpoint induction abstracts the published cyclic-morphism route; the physical residual scan constructs the window used by the full result.

**Theorem 1.1 (Canonical endpoint intervals).**

Lean statement: `D5/S1/Words/Attractors/PeriodicPrefixAttractors.nested_word_endpoint_attractors`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Attractors/PeriodicPrefixAttractors.nested_word_endpoint_attractors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every type α, natural k with 2 ≤ k, w : Nat → List α and U : Nat → Nat, assume: for every m, (w m).length=m; for every m,n with m ≤ n, w m=(w n).take m; U(0)=1; U is strictly monotone; n ↦ U(n+1)-U(n) is monotone; for every n, List.HasPeriod (w(U(n+1)-1)) (U(n)); and for every n with k ≤ n, w(U(n-k)) is a suffix of w(U(n)). Define B(n)=U(n+1)-1, Delta(n)=B(n)-U(n), P(n)=U(n)+(if n < k then 0 else Delta(n-k)), and Gamma(n) as the image of the closed natural interval [n+1-k,n] under j ↦ U(j)-1. For every natural n, P(n) ≤ B(n); and for every natural m with P(n) ≤ m ≤ B(n), IsAttractor (w m) (Gamma(n)). All differences are natural subtraction. The generic theorem assumes these suppliers; result proves them for the original substitution. Lemma 22 and Theorem 23 supply the concrete cyclic-morphism route. This theorem proves the induction for arbitrary coherent prefix families satisfying the displayed structural laws.

**Definition 1.2 (Finite block stack).**

Lean statement: `D5/S1/Words/Attractors/PeriodicPrefixAttractors.descendingBlocks`

*Formalization.* `D5/S1/Words/Attractors/PeriodicPrefixAttractors.descendingBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every type α, word function w : Nat → List α and natural-valued functions U,b : Nat → Nat, descendingBlocks w U b is a function of natural count,t. At (0,t) it is empty. At (count+1,t) it is descendingBlocks w U b count (t+1), concatenated with wordPower (b(t)) (w(U(t))). The physical block order is t+count-1 down to t, with block s equal to wordPower (b(s)) (w(U(s))); multiplicities may be zero. The definition places no monotonicity condition on U.

**Theorem 1.3 (Full-block residual scan).**

Lean statement: `D5/S1/Words/Attractors/PeriodicPrefixAttractors.periodic_residual_scan`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Attractors/PeriodicPrefixAttractors.periodic_residual_scan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every type α, w : Nat → List α and U,b : Nat → Nat, assume: (w m).length=m for every m; w m=(w n).take m whenever m ≤ n; U is strictly monotone; 0 < U(n) for every n; and List.HasPeriod (w(U(n+1)-1)) (U(n)) for every n. For all naturals count,t,N,r and lists X,W : List α, assume 0 < count, X is a prefix of w(U(t+1)-1), X.length < U(t+1)-1, r ≤ X.length, W=descendingBlocks w U b count t concatenated with X, W.length=N+r, and U(t+count)-1 < W.length. Then there exist naturals h,p with t ≤ h < t+count, U(h) ≤ p ≤ N, p-U(h)+(U(h+1)-1) ≤ W.length, (W.drop (p-U(h))).take (U(h+1)-1)=w(U(h+1)-1), and W.drop p is a prefix of w(U(h+1)-1). This is a bounded physical replacement window and actual suffix of W; no positive-block assumption is made on b. The full physical residual-window construction is proved here as a supplier of result; it is not supplied by the published endpoint intervals and carries no independent open-problem or worldwide novelty claim.

## References

- Truth anchor: `D5/S1/Words/Attractors/PeriodicPrefixAttractors.descendingBlocks`
- Truth anchor: `D5/S1/Words/Attractors/PeriodicPrefixAttractors.nested_word_endpoint_attractors`
- Truth anchor: `D5/S1/Words/Attractors/PeriodicPrefixAttractors.periodic_residual_scan`
- Dependency: [D5/S1/Words/Attractors/FiniteWordAttractors](FiniteWordAttractors.md)
