# Composition of Original Controls

## Abstract

Arbitrary finite original controls admit exact chronological concatenation.

**Theorem 1.1 (Exact control and integral composition).**

$$\begin{gathered}\forall b:\operatorname{Base}\left(\right), T,S\in \mathbb{R}, k,chi,K,C:\mathbb{R}\to \mathbb{R},\\{}\operatorname{OC}\left(b, T, k, chi\right)\land \operatorname{OC}\left(b, S, K, C\right)\land k(T)=K(0)\Rightarrow\\{}\operatorname{OC}\left(b, T+S, \operatorname{J}\left(T, k, K\right), \operatorname{J}\left(T, chi, C\right)\right)\land \operatorname{EqOn}\left(\operatorname{J}\left(T, k, K\right), k, [0,T]\right)\land \operatorname{EqOn}\left(\operatorname{J}\left(T, chi, C\right), chi, [0,T]\right)\land\\{}(\forall x\in [0,S], \operatorname{J}\left(T, k, K\right)(T+x)=K(x)\land \operatorname{J}\left(T, chi, C\right)(T+x)=chi(T)+C(x)-C(0))\land\\{}\operatorname{J}\left(T, chi, C\right)(T+S)-\operatorname{J}\left(T, chi, C\right)(0)=chi(T)-chi(0)+C(S)-C(0)\land\\{}(\forall F:\mathbb{R}\to \mathbb{R}, \operatorname{ContinuousOn}\left(F, \operatorname{J}\left(b\right)\right)\Rightarrow \operatorname{I}\left(F, \operatorname{J}\left(T, k, K\right), \operatorname{J}\left(T, chi, C\right), T+S\right)=\operatorname{I}\left(F, k, chi, T\right)+\operatorname{I}\left(F, K, C, S\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalControlComposition.concatenate_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The base b and its positive probability fiber J(b) are those of FiniteRectangleTransport. OriginalControl(b,T,k,chi) requires a finite nonnegative duration, continuity of both real controls on [0,T], k(t) in J(b), finite variation of chi, and either absolute continuity of both controls or continuous finite piecewise C1 controls. A finite piecewise C1 partition may contain repeated times; on every open piece both derivatives agree with continuous rates on the corresponding closed piece.

Write J(T,f,g)(x)=f(x) for x<=T and J(T,f,g)(x)=f(T)+g(x-T)-g(0) for x>T. The same relative second path is therefore applied after the first, with its real phase lift translated to the terminal phase. The probability coordinates agree at the join. Neither path is replaced or reparameterized.

In the formula below OC abbreviates OriginalControl. Prefix equality is equality on [0,T]. The scalar readout I(F,k,chi,L) denotes the integral from zero to L of F(k(t))*chi prime(t). All functions F continuous on the original open probability fiber are included. The theorem asserts the original control condition, both prefix equalities, both exact tail equations, the exact real phase increment, and additive scalar readouts.

A finite piecewise C1 coordinate is absolutely continuous on its complete finite interval. To see this, its derivative is integrable on each piece. Truncating the partition at any intermediate time, applying the interval fundamental theorem on each nonempty truncated piece, and telescoping reconstructs the coordinate as its initial value plus the integral of its derivative. Empty pieces contribute zero. The integral primitive is absolutely continuous. This covers both original alternatives and pairs using different alternatives.

For two absolutely continuous coordinates, paste the derivatives at T and integrate. The resulting primitive equals the first coordinate on [0,T] and the translated second coordinate on [T,T+S]. It gives continuity at the join and finite variation. Strict probability support follows separately from the original first and second paths. The additive readout follows by splitting the interval integral at T, using local derivative equality on each open piece, and translating the second integration interval. Junction values do not affect the integral.

Both zero durations are included. For a pair of loops at one fixed base height, the probability coordinate still begins and ends at that height. If the two exact real phase increments are 2*pi*m and 2*pi*n, the resulting winding is m+n. Taking F to be each original phase-weight component gives additive five-coordinate residuals; taking F(k)=k gives additive signed area. A compatible initial five-phase lift stays compatible under the original transported integral lift. These consequences retain the actual arbitrary controls and their real winding, rather than only their endpoint circle classes.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/OriginalControlComposition.concatenate_original`
- Dependency: [D5/S3/Quantum/Fibers/FiniteRectangleTransport](FiniteRectangleTransport.md)
