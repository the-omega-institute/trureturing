# The sufficient same-graph repair

## Abstract

Translation by an involution centralizing the code in the same Cayley sum graph.

**Theorem 1.1 (Preserving the open-neighbor code).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/CentralizingInvolutionTranslation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/CentralizingInvolutionTranslation.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For a normal connection subset Y of a group G, a code subset C, and b with b*b=1 which commutes with every member of C, C is a total perfect code if and only if its right translate Cb is a total perfect code in the same loopless CS(G,Y). Finite subgroup codes are included. The proof also holds without finiteness or subgroup closure of C.

For h in C, (g*b)*h=g*(h*b), and g*b differs from h precisely when g differs from h*b. Right multiplication by b is its own inverse, so these incidence bijections transport both existence and uniqueness. It is enough that b centralizes C; no commutation with every ambient vertex is assumed.

This is the sufficient repair in section 2.1 of the revised public source, DOI 10.5281/zenodo.23375144. The original version's altered connection set and missing involution hypothesis are not used. Merely normalizing a subgroup is insufficient, as shown by the source's order-32 example. That example and a necessary-and-sufficient classification of all code-preserving translations are separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/CentralizingInvolutionTranslation.result`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion](TotalPerfectCriterion.md)
