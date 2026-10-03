# Nonoscillating Source Endpoints

## Abstract

A nonoscillating word determines strict interior source endpoints in either extremal orientation.

**Theorem 1.1 (Strict endpoints from an actual source word).**

$$\operatorname {SingletonWord}\left(n, sigma, a\right) \land \operatorname {AttainedGeneratorExtrema}\left(m, M, a\right) \land \operatorname {GeneratorInterval}\left(n, m, M, a\right) \land \operatorname {FirstOrientationMap}\left(n, m, M, sigma\right) \land \neg \operatorname {Oscillation}\left(a\right) \implies m < M \land \exists i j , \operatorname {StrictInterior}\left(m, i, j, M\right) \land \operatorname {RemainingSourceMaps}\left(n, m, M, i, j, sigma\right) \land \operatorname {ExteriorFixed}\left(n, m, M, sigma\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeNonoscSourceEndpoints.first_orientation_strict_endpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a be a singleton reduced consecutive word for sigma, with attained minimum m and maximum M, 1<=m<=M<=n, and all letters in [m,M]. Assume sigma sends one-based position M+1 to m and a is not an oscillation. Then m<M. Set i to the one-based inverse image of M+1 under sigma, and j+1 to the image of m. The theorem proves m<i<M and m<j<M, together with sigma(i)=M+1, sigma(m)=j+1, and fixed positions outside [m,M+1]. It assumes no source shape or remaining endpoint equation. Exterior fixedness and injectivity give the weak image bounds. The opposite-extremal-maps theorem excludes i=m and j=M, which would force oscillation. At i=M or j=m, a guarded strand walk forces an attained extremum at the last or first word letter, again forcing oscillation. The m=M case is also excluded by the endpoint-oscillation theorem. The result leaves i and j unordered. For i<=j its data satisfy the shape extractor's endpoint predicate; for j<i they satisfy the order-free fiber theorem's endpoint inputs. Neither case is a global singleton-class count.

**Theorem 1.2 (Strict endpoints in the reflected orientation).**

$$\operatorname {SingletonWord}\left(n, sigma, a\right) \land \operatorname {AttainedGeneratorExtrema}\left(m, M, a\right) \land \operatorname {GeneratorInterval}\left(n, m, M, a\right) \land \operatorname {ReflectedOrientationMap}\left(n, m, M, sigma\right) \land \neg \operatorname {Oscillation}\left(a\right) \implies m < M \land \exists i j , \operatorname {StrictInterior}\left(m, i, j, M\right) \land \operatorname {ReflectedSourceMaps}\left(n, m, M, i, j, sigma\right) \land \operatorname {ExteriorFixed}\left(n, m, M, sigma\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeNonoscSourceEndpoints.reflected_orientation_strict_endpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a be a singleton reduced consecutive word for sigma, with attained minimum m and maximum M, 1<=m<=M<=n, and all letters in [m,M]. Assume sigma(m)=M+1 in one-based positions and a is nonoscillating. Then m<M and there are i,j with m<i<M and m<j<M, sigma(j+1)=m, sigma(M+1)=i, and fixed positions outside [m,M+1]. The witnesses correspond to i=sigma(M+1) and j+1=inverse(sigma)(m). The exact reversal-invariance theorem makes reverse(a) a nonoscillating singleton word for inverse(sigma). Applying the first-orientation theorem there and transporting its equations back proves the displayed maps. No source shape or further position equation is assumed; m=M and boundary witnesses are excluded by the same proof. For i<=j, the data feed the source shape and deletion theorems for inverse(sigma); for j<i, they feed whole-fiber uniqueness there, which word reversal transfers to sigma. A reflected deletion equivalence in the original convention and the global induction are separate obligations.

## References

- Truth anchor: `D5/S1/Words/Permutations/MamedeNonoscSourceEndpoints.first_orientation_strict_endpoints`
- Truth anchor: `D5/S1/Words/Permutations/MamedeNonoscSourceEndpoints.reflected_orientation_strict_endpoints`
- Dependency: [D5/S1/Words/Permutations/MamedeEndpointUniqueness](MamedeEndpointUniqueness.md)
- Dependency: [D5/S1/Words/Permutations/MamedeOppositeExtremalMaps](MamedeOppositeExtremalMaps.md)
