# Total codes supply normal transversals

## Abstract

Normal left transversals obtained from both total perfect subgroup code cases.

**Definition 1.1 (The NLT property).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.NLT`

*Formalization.* `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.NLT` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

NLT(H,G) means that some conjugation-invariant subset T is a left transversal of H. The formal definition uses Mathlib Subgroup.IsComplement: multiplication T times H is a bijection onto G. Equivalently T meets each left coset exactly once. No nonsquare or identity-normalization condition is built into NLT.

**Theorem 1.2 (Both code branches).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

Every total perfect subgroup code in a finite group's normal-connection sum graph is NLT. In the singleton-nonsquare case take T=Y. In the two-element case take T=Y without the identity: the square of 1 puts 1 in Y, removing it leaves exactly one member in the H-coset and changes no outside-coset intersection. Both choices are normal subsets. This is the total-code part of Proposition 4.1 in the source; it does not establish code inheritance, quotient total-code inheritance, the separate perfect-code route, or the full arbitrary-finite-group abelian equivalence.

**Theorem 1.3 (The specified connection transversal).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.transversal_cases`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.transversal_cases` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

If the identity is absent from Y, Y itself is the actual left transversal. If the identity belongs to Y, remove it to obtain the transversal. This distinction retains the exceptional second branch of Theorem 2.1.

**Theorem 1.4 (The additional identity in the count).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.cardinal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.cardinal` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

The actual size of Y equals the subgroup index when 1 is absent and the index plus one when 1 is present. The second branch's additional identity is retained in the connection-set count although the sum graph excludes self-neighbors.

**Theorem 1.5 (Restriction to every intermediate subgroup).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.restrict`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.restrict` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For H contained in M contained in G, restrict a specified normal left transversal T to M. Every M-coset representative selected in G lies in M because its difference from the M-element lies in H. Conjugation by M preserves the intersection. Thus NLT(H,G) implies NLT(H,M) for arbitrary intermediate M, without subnormality. This is Lemma 4.2 of the correction. It is not a statement that quotient or subgroup total-code inheritance follows from NLT.

**Theorem 1.6 (Images under group quotients).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.map`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.map` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For a surjective group homomorphism f whose kernel lies in H, the image of an actual normal transversal is a normal transversal of f(H). The preimage of f(H) is exactly H, so any two putative image representatives in the same coset lift to the same original representative. Surjectivity transports conjugation invariance. Taking f:G to G/N gives NLT(H/N,G/N) whenever N is normal in G and contained in H. This is the quotient statement of Lemma 4.3. It asserts NLT inheritance and supplies no quotient total-code inheritance theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.NLT`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.cardinal`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.map`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.restrict`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.result`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.transversal_cases`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion](TotalPerfectCriterion.md)
