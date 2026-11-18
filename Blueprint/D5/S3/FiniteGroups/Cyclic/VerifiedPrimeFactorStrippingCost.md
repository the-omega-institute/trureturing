# Verified prime-factor stripping cost

## Abstract

The actual stripping program has an exact power-test cost and a logarithmic division budget.

The cost instrument returns a pair: its first component is the exact numeric output of the existing stripFactors program, and its second component counts calls to the power-equality test in the guard. The arithmetic guard 1<p, 0<m, and p∣m is checked first; when it fails, no power test is counted. When it passes, exactly one power test is counted, whether that test succeeds or stops the factor run. A successful test recurses on m/p, preserving the original list order and all original guards.

**Theorem 1.1 (Exact output and logarithmic power-test bound).**

$$\forall G \in \mathit{Typeu},\; [\operatorname{Monoid}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)] \forall x \in G,\; \forall P \in \operatorname{List}\left(\mathit{Nat}\right),\; \forall m \in \mathit{Nat},\; \operatorname{fst}\left(\operatorname{stripFactorsCost}\left(x, P, m\right)\right) = \operatorname{stripFactors}\left(x, P, m\right) \land \operatorname{snd}\left(\operatorname{stripFactorsCost}\left(x, P, m\right)\right) \le \operatorname{length}\left(P\right) + \operatorname{log}\left(2, m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/VerifiedPrimeFactorStrippingCost.stripFactorsCost_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every monoid with decidable equality, element x, finite natural list P, and natural input m, the first component of stripFactorsCost x P m equals stripFactors x P m. Its second component is at most P.length + Nat.log 2 m. The theorem imposes no positivity, order, group, finiteness, factor-coverage, primality, duplicate-freedom, or input-returning hypothesis.

The proof uses a telescoping potential. Every successful recursive division has p≥2 and lowers m to m/p; Nat.log 2 (m/p) is no larger than Nat.log 2 (m/2), while Nat.log 2 (m/2)+1=Nat.log 2 m. A factor pass therefore consumes at most one list-entry unit plus the decrease in the logarithmic potential. Summing this inequality through the left-to-right fold gives the displayed bound. The output projection is proved equal to the original well-founded recursion by strong induction on m.

The count is only for calls to the equality test x^(m/p)=1 in the executable guard. It is not a bit complexity, a count of modular multiplications inside exponentiation, a quantum gate count, or a complete Shor complexity claim. The result is repository-derived; the classical repeated-division algorithm remains literature-attested in the neighboring source.

## References

- Truth anchor: `D5/S3/FiniteGroups/Cyclic/VerifiedPrimeFactorStrippingCost.stripFactorsCost_spec`
- Dependency: [D5/S3/FiniteGroups/Cyclic/VerifiedPrimeFactorStripping](VerifiedPrimeFactorStripping.md)
