# Stable Endpoint Codes

## Abstract

Fixed bounded endpoint codes give exact actual successful fibers and mass sums.

U(n) consists of the actual permutations of Fin(n) avoiding literal 2413 and 3142. State none is U; state some(t) is the actual class with no proper cut of sign t. False is direct and true is skew. A Code(K,H) stores only a stop kind or a sign, an endpoint length r in 1 through K, its actual bounded shape, and a smaller-horizon code. An emitted shape is indecomposable for its sign; a right shape is an arbitrary actual avoider of its bounded size. No terminal permutation or n-indexed data is stored. Code(K,H) is finite even when K or H is zero.

StableCode(t,m,K,H) is the fixed finite subtype satisfying the actual target and state guards. A stop is good when m=0, exhausted for positive m at horizon zero, or cap for positive m at positive horizon. An action needs positive unmet target and parent U or J(not sign). Emission resets the child state to U and target to max(m-r,0); right removal sets the child to J(sign) with unchanged target. For n>H*K, history reconstructs actual positive sizes and states by subtracting each bounded endpoint length.

**Theorem 1.1 (Complete successful supplied-history fibers).**

$$\operatorname{Fiber}\left(c\right)\iff\operatorname{Event}\left(\operatorname{history}\left(c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/StableEndpointCodes.stable_success_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural K,H, every state t, targets m,B and length n with n>H*K+max(2*K,max(m,B)), every stable code c with terminal kind good, and every actual avoider pi, the deterministic classifier fiber of (history(c,n),good) is exactly the complete supplied-history event. Every actual leaf is selected. The recovered minimum cut and its unique actual Cartesian factors force each recorded action. A right action has left length greater than K because its right length is at most K and the parent size is greater than 2*K; left precedence is not assumed. At the good stop, the target is met and the remaining size exceeds B.

**Theorem 1.2 (Stable reconstruction and actual recoding).**

$$\operatorname{compress}\left(\operatorname{history}\left(c\right)\right)=c$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/StableEndpointCodes.stable_code_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every stable code and n>H*K, its reconstructed supplied history has at most H steps, every endpoint size is at most K, and its word at every alphabet and low offset equals the code word. Recompression with its terminal kind recovers the code exactly. A good code emits at least m positions. Above the full threshold, boundedClassify acts on each actual carrier member and its decoded history and terminal kind equal the actual deterministic explorer outcome. Thus every actual outcome is represented by a code from a family independent of n, not by an n-dependent classifier-image catalog.

**Theorem 1.3 (Fixed-family exact restricted sums and successful products).**

$$\operatorname{mass}\left(A\right)=\operatorname{sum}\left(StableCode, \operatorname{fiberMass}\left(A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/StableEndpointCodes.stable_finite_mass_sums` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every state t and natural m,B,K,H,n above n>H*K+max(2*K,max(m,B)), each allowed actual permutation has a unique stable code. For every code, its actual fiber cardinality is exactly the selected terminal-leaf cardinality. Its mass conditional on the actual initial source is history.weight times card(selected leaves)/card(all leaves). On good codes the fiber is the complete history event and its conditional mass is exactly history.weight, the true finite product of actual child-to-parent carrier cardinality ratios. The left numerator is the actual U child count; the right numerator is the actual J(sign) child count, not an independent replacement law.

For every actual event A, its intersection with the initial source has count and full-class uniform mass equal to the finite sums over all StableCode(t,m,K,H) of its intersections with the corresponding fibers. For every predicate on List(Option(Fin B)), the literal first-m-coordinate cylinder mass is the sum of cylinderMass. A successful summand is zero when the predicate rejects the stable code word, and otherwise initial-source mass times the true history product. A non-successful summand retains its actual restricted tested fiber mass. The same fixed-family identity holds for the absolute zero-based test pi(i)!=i at every i<m, using noFixedMass and the code word in alphabet m. Offsets and pending right suffixes remain literal.

Cap fibers are not assigned unrestricted leaf counts: n=4,m=B=H=K=1 in state U has four selected cap leaves out of twenty-two full leaves. The symbolic formulas include zero cap, zero horizon and zero target. Count-ratio asymptotics, sign-half, the infinite coupled law, truncation tails, occupation, discrepancy, filtration, hitting and the full all-length derangement-ratio limit remain distinct mathematical questions.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/StableEndpointCodes.stable_code_transport`
- Truth anchor: `D5/S1/Words/Patterns/Separable/StableEndpointCodes.stable_finite_mass_sums`
- Truth anchor: `D5/S1/Words/Patterns/Separable/StableEndpointCodes.stable_success_fibers`
- Dependency: [D5/S1/Words/Patterns/Separable/CappedExploration](CappedExploration.md)
