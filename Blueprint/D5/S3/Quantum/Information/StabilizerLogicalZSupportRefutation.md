# A stabilizer code without universal logical Z support

## Abstract

A five-qubit stabilizer code has a Z-free word in every nontrivial logical coset.

Pauli consists of the four letters I, X, Y and Z. A word on n qubits is a function from Fin(n), the indices 0 through n − 1, to Pauli. Scalar phases are omitted, as they change neither commutation nor the presence of a literal Z factor. This is the word description of stabilizer elements in Eq. (13). Pauli.rec(a,b,c,d,p) selects a, b, c or d when p is I, X, Y or Z, respectively.

**Definition 1.1 (Phase-free multiplication of words).**

$$\forall n \in \operatorname{\mathit{Nat}},\; \forall u \in (\operatorname{\mathit{Fin}}\left(n\right) \to \operatorname{\mathit{Pauli}}),\; \forall v \in (\operatorname{\mathit{Fin}}\left(n\right) \to \operatorname{\mathit{Pauli}}),\; \operatorname{\mathit{wmul}}\left(u, v\right) = (\lambda (i: \operatorname{\mathit{Fin}}\left(n\right)) \mapsto (\operatorname{\mathit{letterProduct}}\left(u\left(i\right), v\left(i\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.wmul` (`✓ std3`).

*Citation.* Yunzhe Zheng; Dong E. Liu (2025). *From Magic State Distillation to Dynamical Systems*. DOI: [10.22331/q-2025-09-15-1858](https://doi.org/10.22331/q-2025-09-15-1858). URL: <https://arxiv.org/abs/2412.04402v2>.

*Commentary.*

Multiply the letters separately at each qubit, omitting the scalar phase of the Pauli matrix product. In row and column order I, X, Y, Z, the letter-product table has rows (I,X,Y,Z), (X,I,Z,Y), (Y,Z,I,X) and (Z,Y,X,I). The reused letter product is given explicitly by $\forall p \in \operatorname{\mathit{Pauli}},\; \forall q \in \operatorname{\mathit{Pauli}},\; \operatorname{\mathit{letterProduct}}\left(p, q\right) = \operatorname{\mathit{Pauli}.\mathit{rec}}\left(q, \operatorname{\mathit{Pauli}.\mathit{rec}}\left(\operatorname{\mathit{Pauli}.X}, \operatorname{\mathit{Pauli}.I}, \operatorname{\mathit{Pauli}.Z}, \operatorname{\mathit{Pauli}.Y}, q\right), \operatorname{\mathit{Pauli}.\mathit{rec}}\left(\operatorname{\mathit{Pauli}.Y}, \operatorname{\mathit{Pauli}.Z}, \operatorname{\mathit{Pauli}.I}, \operatorname{\mathit{Pauli}.X}, q\right), \operatorname{\mathit{Pauli}.\mathit{rec}}\left(\operatorname{\mathit{Pauli}.Z}, \operatorname{\mathit{Pauli}.Y}, \operatorname{\mathit{Pauli}.X}, \operatorname{\mathit{Pauli}.I}, q\right), p\right)$.

**Definition 1.2 (Commutation from anticommuting positions).**

$$\forall n \in \operatorname{\mathit{Nat}},\; \forall u \in (\operatorname{\mathit{Fin}}\left(n\right) \to \operatorname{\mathit{Pauli}}),\; \forall v \in (\operatorname{\mathit{Fin}}\left(n\right) \to \operatorname{\mathit{Pauli}}),\; (\operatorname{\mathit{Commutes}}\left(u, v\right)) \Leftrightarrow (\sum_{(i: \operatorname{\mathit{Fin}}\left(n\right))} (\operatorname{\mathit{Bool}.\mathit{toNat}}\left(\operatorname{\mathit{anticomm}}\left(u\left(i\right), v\left(i\right)\right)\right)) \bmod 2 = 0)$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.Commutes` (`✓ std3`).

*Citation.* Yunzhe Zheng; Dong E. Liu (2025). *From Magic State Distillation to Dynamical Systems*. DOI: [10.22331/q-2025-09-15-1858](https://doi.org/10.22331/q-2025-09-15-1858). URL: <https://arxiv.org/abs/2412.04402v2>.

*Commentary.*

Two words commute exactly when the number of positions with anticommuting letters is even. Bool.toNat sends false to zero and true to one. The letter predicate is $\forall p \in \operatorname{\mathit{Pauli}},\; \forall q \in \operatorname{\mathit{Pauli}},\; \operatorname{\mathit{anticomm}}\left(p, q\right) = \operatorname{\mathit{if}} ((p = \operatorname{\mathit{Pauli}.I}) \lor (q = \operatorname{\mathit{Pauli}.I})) \operatorname{\mathit{then}} (\operatorname{\mathit{false}}) \operatorname{\mathit{else}} (\operatorname{\mathit{decide}}\left(p \ne q\right))$. Here decide turns the displayed decidable proposition into a Boolean. Thus a position contributes one precisely when its letters are different and both belong to X, Y, Z; all other positions contribute zero.

**Definition 1.3 (Products over subsets of the generators).**

$$\forall n \in \operatorname{\mathit{Nat}},\; \forall r \in \operatorname{\mathit{Nat}},\; \forall g \in (\operatorname{\mathit{Fin}}\left(r\right) \to (\operatorname{\mathit{Fin}}\left(n\right) \to \operatorname{\mathit{Pauli}})),\; \forall w \in (\operatorname{\mathit{Fin}}\left(n\right) \to \operatorname{\mathit{Pauli}}),\; (\operatorname{\mathit{InStabilizer}}\left(g, w\right)) \Leftrightarrow (\exists b \in (\operatorname{\mathit{Fin}}\left(r\right) \to \operatorname{\mathit{Bool}}),\; \operatorname{\mathit{List}.\mathit{foldr}}\left((\lambda (j: \operatorname{\mathit{Fin}}\left(r\right)) \mapsto ((\lambda (w: (\operatorname{\mathit{Fin}}\left(n\right) \to \operatorname{\mathit{Pauli}})) \mapsto (\operatorname{\mathit{if}} (b\left(j\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{wmul}}\left(g\left(j\right), w\right)) \operatorname{\mathit{else}} (w))))), \operatorname{\mathit{Function}.\mathit{const}}\left(\operatorname{\mathit{Fin}}\left(n\right), \operatorname{\mathit{Pauli}.I}\right), \operatorname{\mathit{List}.\mathit{finRange}}\left(r\right)\right) = w)$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.InStabilizer` (`✓ std3`).

*Citation.* Yunzhe Zheng; Dong E. Liu (2025). *From Magic State Distillation to Dynamical Systems*. DOI: [10.22331/q-2025-09-15-1858](https://doi.org/10.22331/q-2025-09-15-1858). URL: <https://arxiv.org/abs/2412.04402v2>.

*Commentary.*

A stabilizer word is a product of a selected subset of the r generator words. The selector b takes Boolean values, with true selecting its generator. Function.const(A, c) returns c at every argument in A. List.finRange(r) lists 0 through r − 1 in order. List.foldr processes this list from the right, starting with the all-I word and multiplying a generator exactly when its selector is true. The empty selection gives the all-I word. This describes the stabilizer elements summed in Eq. (3), modulo phase.

**Definition 1.4 (Commuting independent generators).**

$$\forall n \in \operatorname{\mathit{Nat}},\; \forall r \in \operatorname{\mathit{Nat}},\; \forall g \in (\operatorname{\mathit{Fin}}\left(r\right) \to (\operatorname{\mathit{Fin}}\left(n\right) \to \operatorname{\mathit{Pauli}})),\; (\operatorname{\mathit{IsStabilizerCode}}\left(g\right)) \Leftrightarrow ((\forall a \in \operatorname{\mathit{Fin}}\left(r\right),\; \forall b \in \operatorname{\mathit{Fin}}\left(r\right),\; \operatorname{\mathit{Commutes}}\left(g\left(a\right), g\left(b\right)\right)) \land ((\forall b \in (\operatorname{\mathit{Fin}}\left(r\right) \to \operatorname{\mathit{Bool}}),\; (\operatorname{\mathit{List}.\mathit{foldr}}\left((\lambda (j: \operatorname{\mathit{Fin}}\left(r\right)) \mapsto ((\lambda (w: (\operatorname{\mathit{Fin}}\left(n\right) \to \operatorname{\mathit{Pauli}})) \mapsto (\operatorname{\mathit{if}} (b\left(j\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{wmul}}\left(g\left(j\right), w\right)) \operatorname{\mathit{else}} (w))))), \operatorname{\mathit{Function}.\mathit{const}}\left(\operatorname{\mathit{Fin}}\left(n\right), \operatorname{\mathit{Pauli}.I}\right), \operatorname{\mathit{List}.\mathit{finRange}}\left(r\right)\right) = \operatorname{\mathit{Function}.\mathit{const}}\left(\operatorname{\mathit{Fin}}\left(n\right), \operatorname{\mathit{Pauli}.I}\right)) \Rightarrow (\forall j \in \operatorname{\mathit{Fin}}\left(r\right),\; b\left(j\right) = \operatorname{\mathit{false}})) \land (r < n)))$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.IsStabilizerCode` (`✓ std3`).

*Citation.* Yunzhe Zheng; Dong E. Liu (2025). *From Magic State Distillation to Dynamical Systems*. DOI: [10.22331/q-2025-09-15-1858](https://doi.org/10.22331/q-2025-09-15-1858). URL: <https://arxiv.org/abs/2412.04402v2>.

*Commentary.*

Every pair of generator words must commute. Independence requires that a subset product equal to the all-I word has every selector false. Finally r < n requires fewer generators than qubits, leaving at least one encoded qubit. No further restriction on n or r is imposed.

**Definition 1.5 (The proposed universal logical Z support).**

$$(\mathit{claim}) \Leftrightarrow (\forall n \in \operatorname{\mathit{Nat}},\; \forall r \in \operatorname{\mathit{Nat}},\; \forall g \in (\operatorname{\mathit{Fin}}\left(r\right) \to (\operatorname{\mathit{Fin}}\left(n\right) \to \operatorname{\mathit{Pauli}})),\; (\operatorname{\mathit{IsStabilizerCode}}\left(g\right)) \Rightarrow (\exists L \in (\operatorname{\mathit{Fin}}\left(n\right) \to \operatorname{\mathit{Pauli}}),\; (\forall a \in \operatorname{\mathit{Fin}}\left(r\right),\; \operatorname{\mathit{Commutes}}\left(L, g\left(a\right)\right)) \land ((\neg (\operatorname{\mathit{InStabilizer}}\left(g, L\right))) \land (\forall s \in (\operatorname{\mathit{Fin}}\left(n\right) \to \operatorname{\mathit{Pauli}}),\; (\operatorname{\mathit{InStabilizer}}\left(g, s\right)) \Rightarrow (\exists i \in \operatorname{\mathit{Fin}}\left(n\right),\; \operatorname{\mathit{wmul}}\left(s, L\right)\left(i\right) = \operatorname{\mathit{Pauli}.Z})))))$$

*Formalization.* `D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.claim` (`✓ std3`).

*Citation.* Yunzhe Zheng; Dong E. Liu (2025). *From Magic State Distillation to Dynamical Systems*. DOI: [10.22331/q-2025-09-15-1858](https://doi.org/10.22331/q-2025-09-15-1858). URL: <https://arxiv.org/abs/2412.04402v2>.

*Commentary.*

Every stabilizer code is asserted to have a nontrivial logical word L such that every stabilizer translate s L contains a literal Z factor. Nontrivial means that L commutes with every generator and is not itself a stabilizer word. The conjecture following Proposition 3 and Eq. (23) implies this assertion: any chosen logical Z operator would provide such an L. When more than one qubit is encoded, the assertion asks only for one such word. A Y factor does not count as Z: Eq. (14) associates it with y rather than z.

**Theorem 1.6 (Every nontrivial logical coset has a Z-free translate).**

$$\neg (\mathit{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zheng-liu-2024-logical-z-support-refutation` (refuted) by `D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zheng-liu-2024-logical-z-support-refutation","declaration_gid":"D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yunzhe Zheng; Dong E. Liu (2025). *From Magic State Distillation to Dynamical Systems*. DOI: [10.22331/q-2025-09-15-1858](https://doi.org/10.22331/q-2025-09-15-1858). URL: <https://arxiv.org/abs/2412.04402v2>.

*Commentary.*

Take five qubits and the four generator words XZZXI, IXZZZ, XIXZY and ZXIXY, in that order. They commute pairwise and are independent, and four is less than five. Write S for the set of all their subset products. The words commuting with all four form four cosets of S, with representatives IIIII, XXXXZ, YYYYX and ZZZZY. The first coset is S itself, so a nontrivial logical word belongs to one of the other three.

The three nontrivial representatives have Z-free translates: XXXXZ times IXZZZ is XIYYI, YYYYX times IIIII is YYYYX, and ZZZZY times XZZXI is YIIYY. For any word in one of these cosets, multiply by the same stabilizer word that relates it to its representative, together with the displayed translating word. Every Pauli letter squares to I modulo phase, so the two copies of that stabilizer word cancel. The resulting translate is the corresponding Z-free word. Consequently no nontrivial logical word has a Z factor in every stabilizer translate. This refutes the universal support assertion; Proposition 3 remains a sufficient condition when its support hypothesis holds.

## References

- Truth anchor: `D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.Commutes`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.InStabilizer`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.IsStabilizerCode`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.wmul`
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
