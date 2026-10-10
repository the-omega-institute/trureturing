# ExtendedAvoidanceClosedForm

## Abstract

ExtendedAvoidanceClosedForm for extendably 312-avoiding alternating sign rectangles.

The formulas retain Lean function names and typed binders. Natural subtraction is truncated subtraction; slash between natural numbers is Nat.div. Constructor proof fields and certified cast proofs are suppressed; matrix entries and subtype values are explicit.

**Definition 1.1 (F).**

$$\begin{aligned}\forall (r k d : \mathbb{N}) , F r k d : \mathbb{Z}\\\forall (r k d : \mathbb{N}) , F r k d = ((\sum_{i \in \operatorname{Icc} 1 d} (2 : \mathbb{Z}) ^{(i - 1)} \cdot \operatorname{Ring} . \operatorname{choose} (k : \mathbb{Z}) i \cdot ((\operatorname{if} ((d : \mathbb{Z}) - i) < 0 \operatorname{then} 0 \operatorname{else} \operatorname{Ring} . \operatorname{choose} ((r : \mathbb{Z}) - 2) ((d : \mathbb{Z}) - i) . \operatorname{toNat}) - 2 \cdot (\operatorname{if} ((d : \mathbb{Z}) - i - 2) < 0 \operatorname{then} 0 \operatorname{else} \operatorname{Ring} . \operatorname{choose} ((r : \mathbb{Z}) - 2) ((d : \mathbb{Z}) - i - 2) . \operatorname{toNat}))) + \operatorname{Ring} . \operatorname{choose} (r : \mathbb{Z}) d + (\sum_{i \in \operatorname{range} (d + 1)} (\operatorname{catalan} (2 \cdot i) : \mathbb{Z}) \cdot (\operatorname{if} ((d : \mathbb{Z}) - 1 - 2 \cdot i) < 0 \operatorname{then} 0 \operatorname{else} \operatorname{Ring} . \operatorname{choose} ((r : \mathbb{Z}) - 1 + 2 \cdot i) ((d : \mathbb{Z}) - 1 - 2 \cdot i) . \operatorname{toNat})) + 2 \cdot \sum_{i \in \operatorname{Icc} 1 d} (- 1 : \mathbb{Z}) ^{i} \cdot \operatorname{Ring} . \operatorname{choose} (r : \mathbb{Z}) (d - i))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/ExtendedAvoidanceClosedForm.F` (`✓ std3`).

*Citation.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

Equation (4.2), p. 9. All subtraction between natural numbers is truncated subtraction; subtraction between integers is integer subtraction. binom uses Ring.choose and vanishes for a negative lower index.

**Definition 1.2 (claim).**

$$\begin{aligned}\operatorname{claim} : \operatorname{Prop}\\\operatorname{claim} \Leftrightarrow (\forall r k d : \mathbb{N} , d \le r \to d \le k \to (S r k d : \mathbb{Z}) = F r k d)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/AlternatingSignRectangles/ExtendedAvoidanceClosedForm.claim` (`✓ std3`).

*Citation.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The source states verbatim: “Conjecture 4.5. For integers d ≤ r, k, we have” (p. 9), followed by equation (4.2). The parameters r, k, d range over ℕ, and the literal count is coerced to ℤ.

**Theorem 1.3 (result).**

$$\forall r k d : \mathbb{N} , d \le r \to d \le k \to (S r k d : \mathbb{Z}) = F r k d$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/AlternatingSignRectangles/ExtendedAvoidanceClosedForm.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Höngesberg; Matjaž Konvalinka; Svante Linusson (2026). *Pattern avoidance in alternating sign rectangles I: Extended avoidance*. DOI: [10.48550/arXiv.2610.07442](https://doi.org/10.48550/arXiv.2610.07442). URL: <https://arxiv.org/abs/2610.07442v1>.

*Commentary.*

The closed form follows from the three source recurrences, the large-Schröder power series, the diagonal coefficient identity, and the even-Catalan identity.

## References

- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/ExtendedAvoidanceClosedForm.F`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/ExtendedAvoidanceClosedForm.claim`
- Truth anchor: `D5/S3/Combinatorics/AlternatingSignRectangles/ExtendedAvoidanceClosedForm.result`
- Dependency: [D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators](../../../S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.md)
- Dependency: [D5/S3/Combinatorics/AlternatingSignRectangles/InteriorRecurrence](InteriorRecurrence.md)
- Dependency: [D5/S3/Combinatorics/AlternatingSignRectangles/RecurrenceSeries](RecurrenceSeries.md)
