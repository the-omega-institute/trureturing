# All normal transversals force a solvable group to be abelian

## Abstract

Normal transversals and finite solvable groups.

**Theorem 1.1 (Inheritance by every subgroup).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal.all_restrict`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal.all_restrict` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

If every subgroup of G has a conjugation-invariant left transversal, the same holds inside any intermediate subgroup M. An actual subgroup L of M is first mapped into G and its given normal transversal is then restricted to M. No subnormality is required. This is NLT inheritance, not inheritance of a perfect or total perfect code.

**Theorem 1.2 (All-NLT passes to every quotient).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal.all_map`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal.all_map` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For a surjective group homomorphism, lift each target subgroup to its full preimage. The kernel lies in that preimage, so the specified normal transversal transports to the target subgroup. In particular all-NLT passes to every normal-subgroup quotient. This is an actual subgroup correspondence, not PC or TPC quotient inheritance.

**Theorem 1.3 (A central transversal).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal.central_transversal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal.central_transversal` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

Let H be normal and G/H abelian. Every member t of a specified normal left transversal T is central in G: conjugating t leaves its quotient class fixed, and uniqueness of the actual coset representative forces the conjugate to equal t. Finiteness is unnecessary for this step. This is the central-transversal argument used in source Lemma 4.4.

**Theorem 1.4 (The full finite solvable case).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For every finite solvable group G, if every subgroup is NLT in G, then G is abelian. Strong induction on the actual group cardinal handles the trivial group directly and applies inheritance to the proper derived subgroup in the nontrivial case. Its normal transversal is central; the bijective product of that transversal and the abelian derived subgroup then makes every two elements of G commute. This is Lemma 4.4, not the additional arbitrary-finite-group minimal-counterexample and maximal-subgroup partition argument of Theorem 4.5.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal.all_map`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal.all_restrict`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal.central_transversal`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal.result`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/NormalTransversal](NormalTransversal.md)
