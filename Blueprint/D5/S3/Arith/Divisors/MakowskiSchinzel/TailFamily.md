# Pure and mixed prime-predecessor families

## Abstract

Pure and mixed prime-predecessor families

**Theorem 1.1 (Two parity families have a strict budget).**

$$\forall S \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \forall T \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \forall r \in \mathbb{Q},\; 1 < r \Rightarrow \sum_{z \in S} (\frac{r}{2^{2 \cdot \operatorname{fst}\left(z\right) + 1} \cdot r^{2 \cdot \operatorname{snd}\left(z\right) + 1}}) + \sum_{z \in T} (\frac{r}{2^{2 \cdot \operatorname{fst}\left(z\right) + 2} \cdot r^{2 \cdot \operatorname{snd}\left(z\right) + 2}}) < \frac{r \cdot \left(2 \cdot r + 1\right)}{3 \cdot \left(r^{2} - 1\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.same_parity_geometric_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

The two finite families correspond to odd-odd and even-even positive exponents. For r>1 their combined mass is strictly less than r(2r+1)/(3(r^2-1)). Finite families omit positive terms of the convergent geometric series, so equality is impossible.

**Theorem 1.2 (Even first exponents have a strict budget).**

$$\forall S \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \forall r \in \mathbb{Q},\; 1 < r \Rightarrow \sum_{z \in S} (\frac{r}{2^{2 \cdot \operatorname{fst}\left(z\right) + 2} \cdot r^{\operatorname{snd}\left(z\right) + 1}}) < \frac{r}{3 \cdot \left(r - 1\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.even_first_geometric_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

With the first exponent positive and even, the mass is strictly less than r/(3(r-1)). No bound on either finite set of exponents is required.

**Theorem 1.3 (Comparison of the uniform budgets).**

$$\forall r \in \mathbb{Q},\; 1 < r \Rightarrow \frac{r}{3 \cdot \left(r - 1\right)} < \frac{r \cdot \left(2 \cdot r + 1\right)}{3 \cdot \left(r^{2} - 1\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.even_first_budget_le_same_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

For r>1 the even-first budget is strictly smaller than the combined parity budget. The boundary r=1 cannot be admitted: rational division by zero makes both displayed expressions zero.

**Theorem 1.4 (The exact endpoint of the pure budget).**

$$\forall r \in \mathbb{Q},\; 5 \le r \Rightarrow \left(\frac{r \cdot \left(2 \cdot r + 1\right)}{3 \cdot \left(r^{2} - 1\right)} \le \frac{55}{72} \land \left(\frac{r \cdot \left(2 \cdot r + 1\right)}{3 \cdot \left(r^{2} - 1\right)} = \frac{55}{72} \Leftrightarrow r = 5\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.pure_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

For r>=5 the pure budget is at most 55/72, with equality exactly at r=5. Thus the constant is attained at the endpoint of this range.

**Theorem 1.5 (A cardinality-sensitive mixed budget).**

$$\forall Q \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall r \in \mathbb{N},\; 131 \le r \Rightarrow \left(\operatorname{card}\left(Q\right) \le 42 \Rightarrow \left(\left(\forall q \in \mathbb{N},\; q \in Q \Rightarrow 2 \cdot r \cdot \left(r + 2\right) \le q - 1\right) \Rightarrow \left(\sum_{q \in Q} (\frac{r}{q - 1}) \le \frac{\operatorname{card}\left(Q\right)}{2 \cdot \left(r + 2\right)} \land \frac{\operatorname{card}\left(Q\right)}{2 \cdot \left(r + 2\right)} \le \frac{21}{133}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.mixed_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

For r>=131 and at most forty-two denominators q-1>=2r(r+2), the mass is at most card(Q)/(2(r+2)), and this is at most 21/133. The first bound retains the actual number of terms, including the empty set.

**Theorem 1.6 (An exact parity criterion).**

$$\forall r \in \mathbb{N},\; \forall q \in \mathbb{N},\; \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{mod}\left(r, 3\right) \ne 0 \Rightarrow \left(q - 1 = 2^{a} \cdot r^{b} \Rightarrow \left(\operatorname{mod}\left(q, 3\right) \ne 0 \Leftrightarrow \left(\left(\operatorname{mod}\left(r, 3\right) = 1 \land \operatorname{mod}\left(a, 2\right) = 0\right) \lor \left(\operatorname{mod}\left(r, 3\right) = 2 \land \operatorname{mod}\left(a, 2\right) = \operatorname{mod}\left(b, 2\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.pure_prime_exponent_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

When r is nonzero modulo 3 and q-1=2^a r^b, avoidance of 3 by q is equivalent to the stated parity alternatives. Neither q nor r needs to be prime. Exponents zero are included. If r is 1 modulo 3, a must be even; if r is 2 modulo 3, a and b must have the same parity.

**Theorem 1.7 (A strict pure-family mass bound).**

$$\forall Q \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall r \in \mathbb{N},\; \operatorname{Odd}\left(r\right) \Rightarrow \left(\operatorname{mod}\left(r, 3\right) \ne 0 \Rightarrow \left(5 \le r \Rightarrow \left(\left(\forall q \in \mathbb{N},\; q \in Q \Rightarrow \operatorname{Prime}\left(q\right)\right) \Rightarrow \left(\left(\forall q \in \mathbb{N},\; q \in Q \Rightarrow \left(\exists a \in \mathbb{N},\; \exists b \in \mathbb{N},\; 0 < b \land q - 1 = 2^{a} \cdot r^{b}\right)\right) \Rightarrow \left(\sum_{q \in Q} (\frac{r}{q - 1}) < \frac{r \cdot \left(2 \cdot r + 1\right)}{3 \cdot \left(r^{2} - 1\right)} \land \left(\frac{r \cdot \left(2 \cdot r + 1\right)}{3 \cdot \left(r^{2} - 1\right)} \le \frac{55}{72} \land \left(\operatorname{mod}\left(r, 3\right) = 1 \Rightarrow \sum_{q \in Q} (\frac{r}{q - 1}) < \frac{r}{3 \cdot \left(r - 1\right)}\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.pure_prime_tail_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

For an odd r>=5 not divisible by 3, a finite prime family with q-1=2^a r^b and b>0 has mass strictly below the parity budget. The same budget is at most 55/72. If r is 1 modulo 3, the mass is strictly below the smaller budget r/(3(r-1)). The base r need not be prime.

**Theorem 1.8 (Combining pure and mixed families).**

$$\forall Q \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall r \in \mathbb{N},\; \operatorname{Odd}\left(r\right) \Rightarrow \left(\operatorname{mod}\left(r, 3\right) \ne 0 \Rightarrow \left(131 \le r \Rightarrow \left(\operatorname{card}\left(Q\right) \le 42 \Rightarrow \left(\left(\forall q \in \mathbb{N},\; q \in Q \Rightarrow \operatorname{Prime}\left(q\right)\right) \Rightarrow \left(\left(\forall q \in \mathbb{N},\; q \in Q \Rightarrow \left(\left(\exists a \in \mathbb{N},\; \exists b \in \mathbb{N},\; 0 < b \land q - 1 = 2^{a} \cdot r^{b}\right) \lor 2 \cdot r \cdot \left(r + 2\right) \le q - 1\right)\right) \Rightarrow \left(\sum_{q \in Q} (\frac{r}{q - 1}) < \frac{r \cdot \left(2 \cdot r + 1\right)}{3 \cdot \left(r^{2} - 1\right)} + \frac{42}{2 \cdot \left(r + 2\right)} \land \left(\sum_{q \in Q} (\frac{r}{q - 1}) < \frac{1261}{1368} \land \left(\sum_{q \in Q} (\frac{r}{q - 1}) < \frac{r \cdot \left(2 \cdot r + 1\right)}{3 \cdot \left(r^{2} - 1\right)} + \frac{\operatorname{card}\left(\{q \in Q \mid \neg \exists a \in \mathbb{N},\; \exists b \in \mathbb{N},\; 0 < b \land q - 1 = 2^{a} \cdot r^{b}\}\right)}{2 \cdot \left(r + 2\right)} \land \left(\operatorname{mod}\left(r, 3\right) = 1 \Rightarrow \sum_{q \in Q} (\frac{r}{q - 1}) < \frac{r}{3 \cdot \left(r - 1\right)} + \frac{\operatorname{card}\left(\{q \in Q \mid \neg \exists a \in \mathbb{N},\; \exists b \in \mathbb{N},\; 0 < b \land q - 1 = 2^{a} \cdot r^{b}\}\right)}{2 \cdot \left(r + 2\right)}\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.large_support_tail_of_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Mąkowski and A. Schinzel (1964). *Mąkowski–Schinzel, Colloquium Mathematicum 13, 95–99*. DOI: [10.4064/cm-13-1-95-99](https://doi.org/10.4064/cm-13-1-95-99). URL: <https://doi.org/10.4064/cm-13-1-95-99>.

*Commentary.*

For an odd r>=131 not divisible by 3, at most forty-two primes whose predecessors are either pure or at least 2r(r+2) have mass strictly below the sum of the pure budget and card(M)/(2(r+2)), where M is the non-pure subfamily. When r is 1 modulo 3, the pure budget improves to r/(3(r-1)). Replacing card(M) by 42 gives a uniform bound. The mass bound is the strict inequality 1261/1368<1.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.even_first_budget_le_same_parity`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.even_first_geometric_budget`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.large_support_tail_of_dichotomy`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.mixed_tail_bound`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.pure_prime_exponent_parity`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.pure_prime_tail_budget`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.pure_tail_bound`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily.same_parity_geometric_budget`
