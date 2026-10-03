# Quantitative Teacher Separation under Legal Conditioning

## Abstract

Under rational product window laws with every symbol mass at least a common positive rho, different effective signatures have disagreement at least rho to the fifth power after conditioning on exact seam legality.

Input(n) is Fin(n) to the actual five windows 000,100,010,101,001, written from low to high. Positions start at zero. Legal(x) uses the flattened-bit Fibonacci predicate with false initial bit. All null positions and terminal null windows remain present; there is no End query. A high bit and the following window's low bit cannot both be true.

FiniteResponseLaw(Window) supplies an actual rational mass on every one of the five windows, nonnegativity, and total mass one. laws(i) is the law at position i. Before conditioning, independentSourceLaw(laws) assigns to x the product of laws(i).mass(x(i)) over all positions. legalNormalizer(laws) sums this product over precisely the Legal inputs. conditionedDisagreement(laws,t,u) is the product mass of Legal inputs with teacher(t,x) different from teacher(u,x), divided by that normalizer. The source conditions the full product on all seams together. It imposes no independence assumption after conditioning.

Roles(n) consists of strict triples p<q<r in Fin(n). teacher(t,x) first tests high(x(p)) and low(x(q)), returning 1 when both hold. Otherwise it tests high(x(q)) and low(x(r)), returning 2 when both hold, and 0 otherwise. edge(i,j) is Some(i,j) when i+1<j, and None otherwise. signature(t) is the ordered pair of its two effective edges. Distinct signatures are a premise; distinct role triples alone are insufficient.

**Theorem 1.1 (Positive legal normalizer and a uniform fifth-power disagreement bound).**

$$\forall \left(n: \mathbb{N}\right), \forall \left(laws: \operatorname{Fin}\left(n\right) \to \operatorname{FiniteResponseLaw}\left(Window\right)\right), \forall \left(rho: \mathbb{Q}\right), \left(0 < rho\right) \implies \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \forall \left(a: Window\right), rho \le \operatorname{mass}\left(laws\left(i\right), a\right)\right) \implies \left(\forall \left(t: \operatorname{Roles}\left(n\right)\right), \forall \left(u: \operatorname{Roles}\left(n\right)\right), \left(\operatorname{signature}\left(t\right) \neq \operatorname{signature}\left(u\right)\right) \implies \left(0 < \operatorname{legalNormalizer}\left(laws\right) \land rho^{5} \le \operatorname{conditionedDisagreement}\left(laws, t, u\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LegalConditionedSeparation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalizer is positive because the all-zero input is legal and has positive product mass. An active separating edge is forced by a high window at its first endpoint and a low window at its second endpoint. Zero windows immediately after the first endpoint and immediately before the second preserve every previously legal completion. At most one additional zero endpoint blocks a different active rival edge. The construction uses at most five positions, including overlaps only once. For equal first-edge signatures, the second-edge construction closes both first gates, preserving the actual priority rule. Each completable exterior therefore receives a fixed legal separating completion whose internal product mass is at least rho to the fifth power. Fiber normalization and the original product factorization yield the bound after legal conditioning. The exponent and constant have no optimality claim. A sample guarantee requires a separately specified sampling and label contract.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LegalConditionedSeparation.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/LegalPriorityTeacher](LegalPriorityTeacher.md)
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping](../../ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.md)
