# Noise scales for finite power-controlled spectra

## Abstract

Noise scales for finite power-controlled spectra

**Theorem 1.1 (Information growth and complete recovery).**

$$\operatorname{powerBounds}(q, \lambda, c, C) \land \beta>0 \Rightarrow (\begin{gathered}\forall \alpha\in\mathbb{R}, \operatorname{I}(\alpha, T)-\frac{1}{2}\sum_{i=0}^{n} \operatorname{max}(\alpha-\operatorname{q}(i), 0) \log(\frac{1}{T})=\operatorname{O}(1)\\{}\forall \varepsilon:\mathbb{R}\to\mathbb{R}, (\forall T>0, \varepsilon(T)>0) \Rightarrow (\lim_{T\to0^{+}}\operatorname{R}(\varepsilon, T)=0 \iff \varepsilon(T)=\operatorname{o}(T^{\operatorname{q}(n)}))\\{}\forall \alpha\in\mathbb{R}, (\forall i\in\operatorname{Fin}(n+1), \alpha\neq\operatorname{q}(i)) \Rightarrow \lim_{T\to0^{+}}\operatorname{R}(\alpha, T)=\frac{\operatorname{card}(\{i: \operatorname{q}(i)>\alpha\})}{2 \beta}\end{gathered})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/SpectralNoiseAsymptotics.spectral_noise_asymptotics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n be a nonnegative integer and let i range from zero through n. Choose nonnegative integer powers q(i), with q(i) at most q(n), and real functions lambda(i,T). Fix positive constants beta, c, and C. Assume that for every sufficiently small positive T and every i, c T raised to q(i) is at most lambda(i,T), and lambda(i,T) is at most C T raised to q(i). No continuity is required of these functions. In the display, powerBounds denotes these simultaneous eventual inequalities together with c and C positive and q(i) at most q(n).

For every real alpha define I(alpha,T) as one half the sum over i of log(1+lambda(i,T)/(beta T raised to alpha)). Define R(alpha,T) as one half the sum of T raised to alpha divided by beta T raised to alpha plus lambda(i,T). For any positive variance schedule epsilon on all positive times, define R(epsilon,T) by replacing T raised to alpha in this latter expression with epsilon(T). All logarithms are natural.

For every real alpha, including values equal to one or more occupied powers, the difference between I(alpha,T) and one half the sum of max(alpha-q(i),0) times log(1/T) is bounded as T decreases to zero. R(epsilon,T) tends to zero exactly when epsilon(T) is little-o of T raised to q(n), for every positive schedule without a continuity or power-law assumption. If alpha differs from every q(i), R(alpha,T) tends to the number of indices with q(i) greater than alpha, divided by 2 beta. Repeated powers are counted with their full multiplicity.

Multiplying each logarithm's argument by T raised to max(alpha-q(i),0) puts it in the fixed positive interval from min(1,c/beta) to 1+C/beta. This gives a uniform bound for each logarithmic remainder. With delta(T)=epsilon(T)/T raised to q(n), all risk summands lie between zero and delta(T)/c, while the final summand is at least delta(T)/(beta delta(T)+C). Set v(T)=delta(T)/(beta delta(T)+C). The inverse relation delta=C v/(1-beta v) proves necessity of the recovery condition. The strict-threshold limit follows by separating powers above and below alpha.

## References

- Truth anchor: `D5/S3/Observer/Linear/SpectralNoiseAsymptotics.spectral_noise_asymptotics`
