# Native event coordinates and whole-tree conjugate energy

## Abstract

Native event coordinates and whole-tree conjugate energy

**Theorem 1.1 (Computed integer coordinates and the whole-tree signed conjugate bound).**

$$(\forall L: \operatorname{Type}\left(\right), (\forall T: \operatorname{Tree}\left(L\right), (\forall e: \operatorname{Events}\left(T\right), (((\operatorname{eventMass}\left(T, e\right) = \operatorname{realPhysical}\left(\operatorname{coordinates}\left(T, e\right)\right)) \land (\operatorname{realConjugate}\left(\operatorname{coordinates}\left(T, e\right)\right) = \sum_{p \in \operatorname{Path}\left(T\right)} \sum_{z \in \operatorname{Basis}\left(\right)} \operatorname{if} \operatorname{Apply}\left(e, p, z\right) \operatorname{then} {({-1})}^{\operatorname{exponent}\left(z\right)}*\operatorname{normSq}\left(\operatorname{conjugateAmplitude}\left(\operatorname{branch}\left(T, p, \operatorname{initial}\left(\right)\right), z\right)\right) \operatorname{else} 0)) \land \operatorname{abs}\left(\operatorname{realConjugate}\left(\operatorname{coordinates}\left(T, e\right)\right)\right) \le {(\operatorname{kappa}\left(\right))}^{2*\operatorname{maxCalls}\left(T\right)}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeProtocolEventCoordinates.original_event_coordinates_and_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ian Stewart and David Tall (2025). *Algebraic Number Theory and Fermat's Last Theorem*. DOI: [10.1201/9781003462002](https://doi.org/10.1201/9781003462002).

*Commentary.*

Generality I: these coordinates use the fixed sixteen-bit golden protocol, the inverse-golden relation and its particular cyclotomic extension. The whole-tree estimates are for this instance; no uniform result over arbitrary quadratic fields or gate menus is asserted.

For every terminal-label type L, original native tree T and Boolean terminal event e, coordinates(T,e) is an explicitly computed integer pair A,B in the inverse-golden basis. The physical evaluation is A+B t, with t=phi inverse; its other real evaluation is A-B phi. The displayed theorem identifies the first value with the actually computed raw eventMass, identifies the second value with a signed sum over the same terminal paths and basis words, and bounds its absolute value using L(T)=Tree.maxCalls(T) and kappa=1+2 phi cubed.

The coefficient ring O consists of integer pairs with generator tau satisfying tau squared equals one minus tau. S consists of two O coordinates with generator eta satisfying eta squared equals minus one minus tau eta. These are Mathlib quadratic algebras; their multiplication and both evaluation homomorphisms are proved from the displayed equations. At each full basis word z the coefficient vector h represents the actual amplitude as beta to exponent(z) times physical(h(z)). The exponent is zero or one according to the Hamming parity relative to the actual root at shifted positions 0,4,8. A center-bit flip changes that parity.

The forward update is diagStep(j,z) h(z) plus offStep(j,z) tau to (one minus exponent(z)) h(flip(j,z)). Here diagStep is eta times one plus (eta minus one) times the actual diagonal of P; offStep is tau eta (eta minus one) on the 00 neighboring-control block and zero elsewhere. The proof expands the original number projections and bit flip on all sixteen-bit words and all fourteen addresses. Branch transport follows the original chronological operator product, with nine updates for inverse syntax. A report multiplies each coefficient by its original selector indicator, and all report outcomes remain in the tree.

For H=a+b eta, its quadratic norm in S is a squared minus tau a b plus b squared. The event coordinates sum tau to exponent(z) times this norm only on the selected original terminal coordinates. Under the physical evaluation this is exactly the original squared amplitude. Under tau mapped to minus phi, eta mapped to exp(pi i/5), and beta mapped to i sqrt(phi), it equals minus one to exponent(z) times the embedded squared amplitude. This sign is essential: the second evaluation is not a positive Born mass. No field-membership certificate or assumed event law is present.

The embedded active block has squared operator bound phi to the sixth, obtained by two-coordinate Cauchy-Schwarz and reindexing by the same center-bit involution. The remaining control blocks are zero or identity. The gate norm is therefore at most kappa. Induction on the complete tree sums all measurement energies before comparing the child maxima with the original maximum; selector completeness gives exact energy conservation even for non-surjective selectors. This proves a whole-tree bound with no leaf, report or branch-count factor. Zero-mass deep branches and nine-cost calls retain their syntactic resource cost.

The actual cut construction belongs to NativeProtocolBornNormalization. It uses the same branch coefficient representation exposed by original_branch_evaluations; the complete nonphysical energy budget remains available for the determinant estimate. Relative root parity must split across the exact retained-position equivalence; physical conjugation fixes beta while the nonphysical beta is imaginary, so a signed Gram identity is required. The scalar event theorem supplies neither a cut determinant bound nor a full-rank inference.

This event theorem does not identify an original cut reduction or prove its determinant or spectral lower bounds. It does not construct the actual chi state, Petz comparison, full record-law bridge or Born normalization, and it does not prove that the ninth gate power is the semantic inverse.

**Lemma 1.2 (The actual branch amplitudes and their complete nonphysical energy budget).**

$$(\forall L: \operatorname{Type}\left(\right), (\forall T: \operatorname{Tree}\left(L\right), ((\forall p: \operatorname{Path}\left(T\right), (\operatorname{amplitude}\left(\operatorname{branch}\left(T, p, \operatorname{initial}\left(\right)\right)\right) = \operatorname{mulVec}\left(\operatorname{operator}\left(T, p\right), \operatorname{omega0}\left(\right)\right))) \land \operatorname{treeEnergy}\left(T, \operatorname{initial}\left(\right)\right) \le {(\operatorname{kappa}\left(\right))}^{2*\operatorname{maxCalls}\left(T\right)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeProtocolEventCoordinates.original_branch_evaluations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ian Stewart and David Tall (2025). *Algebraic Number Theory and Fermat's Last Theorem*. DOI: [10.1201/9781003462002](https://doi.org/10.1201/9781003462002).

*Commentary.*

For every original tree and each unchanged original path, evaluating the computed coefficient branch gives the chronological original operator product on omega0. The sum of the squared nonphysical branch norms over the complete original tree is at most kappa to twice maxCalls. The branch identity and complete-tree energy bound supply the coefficient factorization and conjugate-embedding estimate for the same acquired-event cut in NativeProtocolBornNormalization.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/NativeProtocolEventCoordinates.original_branch_evaluations`
- Truth anchor: `D5/S3/Quantum/Dynamics/NativeProtocolEventCoordinates.original_event_coordinates_and_bound`
- Dependency: [D5/S3/Quantum/Dynamics/NativeProtocolGraft](NativeProtocolGraft.md)
