# Critical-Zero Transverse Gap

## Abstract

A critical-line zero has a transverse gap whose order is twice its multiplicity.

**Theorem 1.1 (The transverse gap at a critical zero).**

$$\forall r: \mathbb{N}, t_{0}: \mathbb{R},\\{}0 < r \land(\forall j: \mathbb{N}, j < r \Rightarrow \operatorname{iteratedDeriv}\left(j, criticalXi, t_{0}\right) = 0) \land\operatorname{iteratedDeriv}\left(r, criticalXi, t_{0}\right) \neq 0 \Rightarrow \begin{gathered}(\forall m: \mathbb{N}, m < r \Rightarrow \operatorname{normalJet}\left(t_{0}, m\right) = 0) \land\\{}\operatorname{normalJet}\left(t_{0}, r\right) = \frac{\operatorname{iteratedDeriv}\left(r, criticalXi, t_{0}\right)}{\operatorname{factorial}\left(r\right)}^{2} \land\\{}0 < \operatorname{normalJet}\left(t_{0}, r\right) \land\\{}\operatorname{IsBigOAtZero}\left((delta \mapsto \operatorname{normalIntensity}\left(delta, t_{0}\right) - \frac{\operatorname{iteratedDeriv}\left(r, criticalXi, t_{0}\right)}{\operatorname{factorial}\left(r\right)}^{2} \cdot delta^{2r}), (delta \mapsto delta^{2r + 2})\right) \land\\{}(r = 1 \Rightarrow \operatorname{IsBigOAtZero}\left((delta \mapsto \operatorname{normalIntensity}\left(delta, t_{0}\right) - \operatorname{iteratedDeriv}\left(1, criticalXi, t_{0}\right)^{2} \cdot delta^{2}), (delta \mapsto delta^{4})\right))\end{gathered}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalZeroTransverseGap.critical_zero_transverse_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let t0 be a zero of the canonical critical-line completed-xi reading with positive multiplicity r: all derivatives below r vanish and the derivative of order r is nonzero. Every normal jet below r then vanishes, while the depth-r jet is the strictly positive square of the leading Taylor coefficient.

The two final public conjuncts concern the actual norm-squared normal intensity. Its leading transverse term has degree 2r with remainder of order 2r+2; at a simple zero this becomes the squared first derivative times the displacement squared, with quartic remainder.

The proof imports the canonical normal-jet convolution formula. It also uses conjugate reflection to prove evenness of the actual intensity and applies the pinned Taylor remainder theorem to that smooth function.

## References

- Truth anchor: `D5/S3/Zeros/CriticalZeroTransverseGap.critical_zero_transverse_gap`
- Dependency: [D5/S3/Zeros/NormalJetFormula](NormalJetFormula.md)
