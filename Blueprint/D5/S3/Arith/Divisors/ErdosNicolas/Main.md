# The Erdős–Nicolas conjecture

## Abstract

The Erdős–Nicolas divisor difference conjecture

**Theorem 1.1 (Every integer above 5040 satisfies the strict inequality).**

$$\forall n \in \mathbb{N},\; 5040 < n \Rightarrow \operatorname{Hhat}\left(n\right) < \operatorname{card}\left(\operatorname{divisors}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas` (`✓ std3`). ∎

*Resolves.* `Problems/erdos-nicolas-1989-divisor-difference-sum` (proved) by `D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"erdos-nicolas-1989-divisor-difference-sum","declaration_gid":"D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

Page 390 of the cited source: “We conjecture that for n > 5040, we have Ĥ(n) < τ(n).” Here Ĥ(n) is the unordered reciprocal gap sum over all positive divisors and τ(n) is their number. A rational positive semidefinite kernel controls cross-block interactions. Strong induction and exact finite certificates discharge every branch without an extra analytic or numerical hypothesis. The proof handles arbitrary prime exponent order, including noncanonical integers. The six certificate propositions are proved by the imported data modules and supplied to good_of_finite_certificates; none remain as assumptions of this theorem. The conditional classification also identifies the exact fourteen positive exceptions. Numerical observations, literature priority, and further extensions are distinguished in the problem dossier.

## References

- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas`
