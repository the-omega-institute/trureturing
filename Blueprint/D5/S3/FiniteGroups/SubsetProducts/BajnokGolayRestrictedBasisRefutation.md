# A Golay quotient refutes the restricted-basis classification

## Abstract

The Golay quotient has a perfect restricted three-basis of size twenty-three and lies outside Bajnok's proposed families.

A perfect restricted s-basis represents every group element uniquely as the sum of at most s distinct elements of the basis, with the empty subset representing zero. Here the group is the quotient of binary words of length twenty-three by the punctured binary Golay code.

**Definition 1.1 (Binary words of length twenty-three).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.ShortWord`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.ShortWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bela Bajnok (2022). *A Walk Through Some Newer Parts of Additive Combinatorics*. DOI: [10.48550/arXiv.2211.01893](https://doi.org/10.48550/arXiv.2211.01893). URL: <https://arxiv.org/abs/2211.01893v1>.

*Commentary.*

ShortWord is Fin 23 -> F2, where F2 is ZMod 2.

**Definition 1.2 (Deleting the parity coordinate).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.puncturedEncode`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.puncturedEncode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bela Bajnok (2022). *A Walk Through Some Newer Parts of Additive Combinatorics*. DOI: [10.48550/arXiv.2211.01893](https://doi.org/10.48550/arXiv.2211.01893). URL: <https://arxiv.org/abs/2211.01893v1>.

*Commentary.*

puncturedEncode is the F2-linear map from GolayEncoder.Message to ShortWord obtained by composing the existing twenty-four-coordinate GolayEncoder.encode with restriction along Fin.castSucc : Fin 23 -> Fin 24. Thus the final parity coordinate is deleted, and the original twelve-dimensional message space is retained.

**Definition 1.3 (The actual punctured Golay code).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.puncturedCode`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.puncturedCode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bela Bajnok (2022). *A Walk Through Some Newer Parts of Additive Combinatorics*. DOI: [10.48550/arXiv.2211.01893](https://doi.org/10.48550/arXiv.2211.01893). URL: <https://arxiv.org/abs/2211.01893v1>.

*Commentary.*

puncturedCode is the submodule equal to the range of puncturedEncode. The original parity-extension identity makes this encoder injective. Its code therefore has 4096 elements. Deleting one coordinate lowers weight by at most one, so the original minimum weight eight gives minimum weight at least seven.

**Definition 1.4 (The additive quotient group).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.GolayGroup`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.GolayGroup` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bela Bajnok (2022). *A Walk Through Some Newer Parts of Additive Combinatorics*. DOI: [10.48550/arXiv.2211.01893](https://doi.org/10.48550/arXiv.2211.01893). URL: <https://arxiv.org/abs/2211.01893v1>.

*Commentary.*

GolayGroup is the submodule quotient ShortWord / puncturedCode, with its induced finite abelian additive group structure.

**Theorem 1.5 (The quotient has order 2048).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.golay_group_card`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.golay_group_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bela Bajnok (2022). *A Walk Through Some Newer Parts of Additive Combinatorics*. DOI: [10.48550/arXiv.2211.01893](https://doi.org/10.48550/arXiv.2211.01893). URL: <https://arxiv.org/abs/2211.01893v1>.

*Commentary.*

Nat.card GolayGroup = 2048. The ambient group has 2^23 elements, and the code has 2^12 elements; the quotient cardinality formula gives 2^11.

**Theorem 1.6 (All sums of at most three elements).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.golay_perfect_restricted_basis`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.golay_perfect_restricted_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bela Bajnok (2022). *A Walk Through Some Newer Parts of Additive Combinatorics*. DOI: [10.48550/arXiv.2211.01893](https://doi.org/10.48550/arXiv.2211.01893). URL: <https://arxiv.org/abs/2211.01893v1>.

*Commentary.*

There exists A : Finset GolayGroup with A.card = 23 and IsPerfectRestrictedBasis 3 A. The basis consists of the twenty-three coordinate-vector classes. The general minimum-distance argument applies because six is less than every nonzero codeword weight, and 1 + 23 + choose(23,2) + choose(23,3) = 2048.

**Definition 1.7 (The proposed group families).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.ListedFamily`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.ListedFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bela Bajnok (2022). *A Walk Through Some Newer Parts of Additive Combinatorics*. DOI: [10.48550/arXiv.2211.01893](https://doi.org/10.48550/arXiv.2211.01893). URL: <https://arxiv.org/abs/2211.01893v1>.

*Commentary.*

For G : Type with AddCommGroup G, naturals s,m, and R : Type with AddCommGroup R, ListedFamily G s m R is the disjunction: Nat.card G = 2^m; or a nonempty type of additive equivalences G to ZMod (2^(s+1)-1); or such an equivalence to Fin (2*s) -> F2; or such an equivalence to (Fin (2*s-2) -> R) times ZMod 4. The printed survey has R equal to the integers in its last family; the companion paper gives the intended finite family with R equal to F2.

**Definition 1.8 (Conjecture 22 as printed).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.claim`

*Formalization.* `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bela Bajnok (2022). *A Walk Through Some Newer Parts of Additive Combinatorics*. DOI: [10.48550/arXiv.2211.01893](https://doi.org/10.48550/arXiv.2211.01893). URL: <https://arxiv.org/abs/2211.01893v1>.

*Commentary.*

claim is the following closed proposition. For every G : Type with AddCommGroup G, Fintype G and DecidableEq G, and all naturals m,s with 2 <= m and 2 <= s, there exists A : Finset G with A.card = m and IsPerfectRestrictedBasis s A if and only if ListedFamily G s m Int. Decidable equality supplies the finite-set representation. The final integer-power family is retained literally.

**Theorem 1.9 (Both readings fail for the same group).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.golay_counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.golay_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bela Bajnok (2022). *A Walk Through Some Newer Parts of Additive Combinatorics*. DOI: [10.48550/arXiv.2211.01893](https://doi.org/10.48550/arXiv.2211.01893). URL: <https://arxiv.org/abs/2211.01893v1>.

*Commentary.*

There exists A : Finset GolayGroup with A.card = 23, IsPerfectRestrictedBasis 3 A, not ListedFamily GolayGroup 3 23 Int, and not ListedFamily GolayGroup 3 23 F2. The proposed finite orders are 2^23, 15 and 64, all different from 2048; the literal integer-power last family is infinite. The parameters also answer Bajnok--Berson--Just Question 11 affirmatively, since 23 >= 2*3+2.

**Theorem 1.10 (The classification is false).**

Lean statement: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bajnok-2022-perfect-restricted-bases-conjecture-22-golay` (refuted) by `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bajnok-2022-perfect-restricted-bases-conjecture-22-golay","declaration_gid":"D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Bela Bajnok (2022). *A Walk Through Some Newer Parts of Additive Combinatorics*. DOI: [10.48550/arXiv.2211.01893](https://doi.org/10.48550/arXiv.2211.01893). URL: <https://arxiv.org/abs/2211.01893v1>.

*Commentary.*

result has type Not claim. Apply the necessary direction of the proposed equivalence to GolayGroup, m = 23 and s = 3. The perfect restricted basis gives a listed family, contradicting the counterexample. The obstruction also excludes the intended finite final family, so the refutation does not rely on its printed missing subscript.

## References

- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.GolayGroup`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.ListedFamily`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.ShortWord`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.claim`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.golay_counterexample`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.golay_group_card`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.golay_perfect_restricted_basis`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.puncturedCode`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.puncturedEncode`
- Truth anchor: `D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.result`
- Dependency: [D5/S3/Arith/Lattices/Golay/GolayEncoder](../../Arith/Lattices/Golay/GolayEncoder.md)
- Dependency: [D5/S3/FiniteGroups/SubsetProducts/BinaryCodePerfectRestrictedBasis](BinaryCodePerfectRestrictedBasis.md)
