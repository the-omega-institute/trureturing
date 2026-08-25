# Small Prime Channel Optimality

## Abstract

The first m primes maximize information among m complete equal-cost channels.

**Theorem 1.1 (The first m prime channels maximize total information).**

$$\begin{gathered}\forall s \in (1, \infty), H: (1, \infty) \to \operatorname{Primes} \to \mathbb{R},\\{}m \in \mathbb{N}, c: \operatorname{OrderEmbedding}(\operatorname{Fin}(m), \mathbb{N}),\\{}(\forall p, r \in \operatorname{Primes}, p < r \Rightarrow H(s, r) < H(s, p)) \land (\forall i \in \operatorname{Fin}(m), \operatorname{Prime}(c(i))) \Rightarrow\\{}\sum_{i\in \operatorname{Fin}(m)} H(s, c(i)) \leq \sum_{i\in \operatorname{Fin}(m)} H(s, \operatorname{prime}(i)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/SmallPrimeChannelOptimality.small_prime_channel_optimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parameter s is publicly restricted to the open interval above one. The function H assigns expected information to every complete prime channel at each such parameter, and the displayed premise states its strict decrease as the prime grows.

An order embedding c from Fin(m) into the natural numbers represents an increasing choice of exactly m distinct channels. The public primality premise ensures that every selected index is a prime; the shared cardinality is the equal-cost budget constraint.

The canonical increasing enumeration of the prime subtype is pointwise no larger than any such ordered choice. Strict decrease of H turns that comparison around, and summing the pointwise inequalities proves the displayed maximum.

## References

- Truth anchor: `D5/S3/Observer/ArithmeticTomography/SmallPrimeChannelOptimality.small_prime_channel_optimality`
