# Hanna A232696: congruences of exponential coefficients

## Abstract

Both nominated congruences hold for every factorial-normalized coefficient of OEIS A232696.

**Definition 1.1 (The rational formal-series equation).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSolution}\left(A\right) \Leftrightarrow \left(\operatorname{constantCoeff}\left(A\right) = 1 \land \operatorname{PowerSeries}.\operatorname{derivative}\left(A\right) = \operatorname{PowerSeries}.\operatorname{subst}\left(A, X \cdot \operatorname{Inv}.\operatorname{inv}\left(\operatorname{PowerSeries}.\operatorname{derivative}\left(A\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaA232696Congruences.IsSolution` (`✓ std3`).

*Citation.* Paul D. Hanna (2013). *Derivative-substitution exponential generating functions A232694, A232695, A232696 and A232686*. URL: <https://oeis.org/A232694>.

*Commentary.*

%N A232696 E.g.f. A(x) satisfies: A'(x) = A(x/A'(x)) with A(0)=1. %C A232696  CONJECTURES. %C A232696 a(n) == 0 (mod 2) for n>=4. %C A232696 a(n) == 0 (mod 2^2) for n>=10. %C A232696 a(n) == 0 (mod 2^3) for n>=18. %C A232696 a(n) == 0 (mod 2^k) for n>=(8*n-6) for k>1. %e A232696 E.g.f.: A(x) = 1 + x + x^2/2! - x^3/3! + 2*x^4/4! + 6*x^5/5! - 264*x^6/6! + 5370*x^7/7! +... OEIS A232696 has no page number; these are its NAME, COMMENTS and EXAMPLE lines. All indices are natural numbers, starting at zero. The displayed factorials define the exponential coefficients. The formal derivative and substitution act in PowerSeries Rat; no analytic convergence is assumed.

**Definition 1.2 (The two congruences).**

$$claim = \left(\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSolution}\left(A\right) \Rightarrow \left(\exists a \in \mathbb{N} \to \mathbb{Z},\; \left(\forall n \in \mathbb{N},\; \operatorname{eCoeff}\left(A, n\right) = (a\left(n\right): \mathbb{Q})\right) \land \left(\left(\forall n \in \mathbb{N},\; 4 \le n \Rightarrow (2: \mathbb{Z}) \mid a\left(n\right)\right) \land \left(\forall n \in \mathbb{N},\; 10 \le n \Rightarrow (4: \mathbb{Z}) \mid a\left(n\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaA232696Congruences.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2013). *Derivative-substitution exponential generating functions A232694, A232695, A232696 and A232686*. URL: <https://oeis.org/A232694>.

*Commentary.*

%N A232696 E.g.f. A(x) satisfies: A'(x) = A(x/A'(x)) with A(0)=1. %C A232696  CONJECTURES. %C A232696 a(n) == 0 (mod 2) for n>=4. %C A232696 a(n) == 0 (mod 2^2) for n>=10. %C A232696 a(n) == 0 (mod 2^3) for n>=18. %C A232696 a(n) == 0 (mod 2^k) for n>=(8*n-6) for k>1. %e A232696 E.g.f.: A(x) = 1 + x + x^2/2! - x^3/3! + 2*x^4/4! + 6*x^5/5! - 264*x^6/6! + 5370*x^7/7! +... The equation is encoded by IsSolution. The integer sequence a is required to have eCoeff(A,n)=(a(n):Rat) at every index, so integrality is part of the conclusion. Divisibility expresses precisely the two nominated residue assertions. Other COMMENTS assertions, when present, are outside this proposition.

**Theorem 1.3 (The congruences hold at every index).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{IsSolution}\left(A\right) \Rightarrow \left(\exists a \in \mathbb{N} \to \mathbb{Z},\; \left(\forall n \in \mathbb{N},\; \operatorname{eCoeff}\left(A, n\right) = (a\left(n\right): \mathbb{Q})\right) \land \left(\left(\forall n \in \mathbb{N},\; 4 \le n \Rightarrow (2: \mathbb{Z}) \mid a\left(n\right)\right) \land \left(\forall n \in \mathbb{N},\; 10 \le n \Rightarrow (4: \mathbb{Z}) \mid a\left(n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaA232696Congruences.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2013). *Derivative-substitution exponential generating functions A232694, A232695, A232696 and A232686*. URL: <https://oeis.org/A232694>.

*Commentary.*

An integral triangular recurrence transfers the residues of an approximate solution to every exact solution. Multiplication by the third or ninth power of the approximate derivative makes the residual polynomial. Its exponential coefficients are divisible by two or four, respectively. Cancellation of the integral series with constant coefficient one gives the two divisibility tails.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/HannaA232696Congruences.IsSolution`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaA232696Congruences.claim`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaA232696Congruences.result`
- Dependency: [D5/S1/Recurrence/Residue/HannaEGFMachinery](HannaEGFMachinery.md)
