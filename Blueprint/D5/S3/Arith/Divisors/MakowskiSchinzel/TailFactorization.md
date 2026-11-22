# The least odd predecessor prime controls the tail

## Abstract

The least odd predecessor prime controls the tail

**Theorem 1.1 (A strict mass bound from least-prime control).**

$$\forall Q \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall r \in \mathbb{N},\; \operatorname{Prime}\left(r\right) \Rightarrow \left(131 \le r \Rightarrow \left(\operatorname{card}\left(Q\right) \le 42 \Rightarrow \left(\left(\forall q \in \mathbb{N},\; q \in Q \Rightarrow \operatorname{Prime}\left(q\right)\right) \Rightarrow \left(\left(\forall q \in \mathbb{N},\; q \in Q \Rightarrow r \mid q - 1\right) \Rightarrow \left(\left(\forall q \in \mathbb{N},\; q \in Q \Rightarrow \left(\forall s \in \mathbb{N},\; \operatorname{Prime}\left(s\right) \Rightarrow \left(s \ne 2 \Rightarrow \left(s \mid q - 1 \Rightarrow r \le s\right)\right)\right)\right) \Rightarrow \left(\sum_{q \in Q} (\frac{r}{q - 1}) < \frac{r \cdot \left(2 \cdot r + 1\right)}{3 \cdot \left(r^{2} - 1\right)} + \frac{42}{2 \cdot \left(r + 2\right)} \land \left(\sum_{q \in Q} (\frac{r}{q - 1}) < \frac{1261}{1368} \land \left(\sum_{q \in Q} (\frac{r}{q - 1}) < \frac{r \cdot \left(2 \cdot r + 1\right)}{3 \cdot \left(r^{2} - 1\right)} + \frac{\operatorname{card}\left(\{q \in Q \mid \neg \exists a \in \mathbb{N},\; \exists b \in \mathbb{N},\; 0 < b \land q - 1 = 2^{a} \cdot r^{b}\}\right)}{2 \cdot \left(r + 2\right)} \land \left(\operatorname{mod}\left(r, 3\right) = 1 \Rightarrow \sum_{q \in Q} (\frac{r}{q - 1}) < \frac{r}{3 \cdot \left(r - 1\right)} + \frac{\operatorname{card}\left(\{q \in Q \mid \neg \exists a \in \mathbb{N},\; \exists b \in \mathbb{N},\; 0 < b \land q - 1 = 2^{a} \cdot r^{b}\}\right)}{2 \cdot \left(r + 2\right)}\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFactorization.large_support_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

Let r>=131 be prime and let Q contain at most forty-two primes q. Assume r divides every q-1 and no odd prime divisor of any q-1 is smaller than r. Then the total mass r/(q-1) is strictly less than the pure geometric budget plus card(M)/(2(r+2)), where M consists of the non-pure predecessors. If r is 1 modulo 3 the pure budget is r/(3(r-1)). The bound with 42 in place of card(M) also holds, as does the strict bound 1261/1368. Factoring q-1 splits it into a pure power family and a family containing a second odd prime at least r+2.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFactorization.large_support_tail`
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily](TailFamily.md)
