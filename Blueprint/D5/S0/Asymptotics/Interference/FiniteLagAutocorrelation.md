# Finite Lag Autocorrelation

## Abstract

A finite real signal has its exact lag autocorrelation as the Fourier coefficients of its squared modulus.

**Theorem 1.1 (Finite signals expand by lag autocorrelation).**

$$\forall T \in \mathbb{N}, f: \operatorname{Fin}\left(T + 1\right) \Rightarrow \mathbb{R}, theta \in \mathbb{R},\ \text{let p : \mathbb{C}[X, X^{-1}] = \sum_{0 \leq n \leq T} f_{n} X^{n}, A = \operatorname{invert}\left(p\right) \times p},\ (\forall m \in \mathbb{Z}, A_{m} = \sum_{n \in \operatorname{Fin}\left(T + 1\right)} f_{n} p_{n + m}) \land\\{}(\operatorname{normSq}\left(\operatorname{finiteSignal}\left(f, \operatorname{exp}\left(i\,theta\right)\right)\right) = \sum_{-T \leq m \leq T} A_{m} \operatorname{exp}\left(i\,theta\right)^{m}).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/Interference/FiniteLagAutocorrelation.finite_lag_autocorrelation_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real signal indexed by Fin(T+1), p is its Laurent coefficient polynomial, extended by zero away from indices zero through T. The Laurent product A = invert(p) times p is constructed from that signal.

The first public conjunct proves that the coefficient A_m is the lag sum of f_n times f_(n+m), with the zero extension supplied by p. The second public conjunct evaluates the same Laurent product on the unit circle and obtains the squared modulus over exactly the possible lags.

The proof imports the earlier finite pairwise expansion only as the canonical finite-signal primitive. Laurent convolution, inversion, support bounds, and unit-circle conjugation establish the stronger lag-indexed statement.

## References

- Truth anchor: `D5/S0/Asymptotics/Interference/FiniteLagAutocorrelation.finite_lag_autocorrelation_expansion`
- Dependency: [D5/S0/Asymptotics/Interference/FiniteAutocorrelation](FiniteAutocorrelation.md)
