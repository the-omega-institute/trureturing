# Prime-Dephasing Refinement Absorption

## Abstract

Finite profile observations form an absorbing family of record-channel dephasings.

**Definition 1.1 (Restricted prime profile).**

Lean statement: `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.restrictedPrimeProfile`

*Formalization.* `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.restrictedPrimeProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict each finite system address's supplied valuation profile to the observed finite index set S.

**Definition 1.2 (Profile-class representative).**

Lean statement: `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.profileClassRepresentative`

*Formalization.* `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.profileClassRepresentative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose the least finite address in the same restricted-profile fiber. This finite representative avoids any finiteness assumption on the valuation's codomain.

**Definition 1.3 (Orthogonal profile record).**

Lean statement: `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.orthogonalProfileRecord`

*Formalization.* `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.orthogonalProfileRecord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Encode every profile fiber by the standard basis vector at its canonical representative, so equal fibers have Gram overlap one and distinct fibers have overlap zero.

**Definition 1.4 (Finite-prime dephasing channel).**

Lean statement: `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.primeDephasing`

*Formalization.* `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.primeDephasing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the repository's canonical recordChannel to the orthogonal record of the S-restricted valuation profile. No second channel formula is introduced.

**Theorem 1.5 (Refinement absorption).**

$$\begin{aligned}S \subseteq T \Rightarrow\\E_{T} \circ E_{S} = E_{S} \circ E_{T} \land\\E_{T} \circ E_{S} = E_{T} \land\\E_{S} \circ E_{T} = E_{T}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.prime_dephasing_refinement_absorption` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If S is contained in T, equality of T-profiles implies equality of S-profiles. Entrywise, the finer zero-one Gram mask therefore absorbs the coarser mask in either order.

The statement records all three requested equalities: commutation, finer-after-coarser absorption, and coarser-after-finer absorption.

**Lemma 1.6 (Idempotence at equal index sets).**

$$E_{S} \circ E_{S} = E_{S}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.prime_dephasing_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specializing refinement to S equals T recovers idempotence directly from the absorption theorem.

**Lemma 1.7 (Empty observation is the identity).**

$$E_{\emptyset} = id.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.prime_dephasing_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All profiles restricted to the empty set are equal, so no matrix entry is discarded.

**Lemma 1.8 (The full index set absorbs every subset).**

$$\begin{aligned}E_{univ} \circ E_{S} = E_{S} \circ E_{univ} \land\\E_{univ} \circ E_{S} = E_{univ} \land\\E_{S} \circ E_{univ} = E_{univ}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.prime_dephasing_univ_absorption` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite index type, every S is contained in the full set. The three refinement equalities therefore hold with T equal to the universe.

**Proposition 1.9 (The refinement premise is necessary).**

$$\neg{\{1\} \subseteq \emptyset} \land E_{\emptyset} \circ E_{\{1\}} \neq E_{\emptyset}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.refinement_subset_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On two addresses, a singleton observed index distinguishes the addresses while the empty target observation preserves their off-diagonal entry. Thus finer-first absorption fails when S is not contained in T.

## References

- Truth anchor: `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.orthogonalProfileRecord`
- Truth anchor: `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.primeDephasing`
- Truth anchor: `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.prime_dephasing_empty`
- Truth anchor: `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.prime_dephasing_idempotent`
- Truth anchor: `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.prime_dephasing_refinement_absorption`
- Truth anchor: `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.prime_dephasing_univ_absorption`
- Truth anchor: `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.profileClassRepresentative`
- Truth anchor: `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.refinement_subset_is_necessary`
- Truth anchor: `D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.restrictedPrimeProfile`
- Dependency: [D5/S3/Quantum/FixedAlgebra/SingletonRecordClassicality](SingletonRecordClassicality.md)
