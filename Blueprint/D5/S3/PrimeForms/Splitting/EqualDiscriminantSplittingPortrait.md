# Equal-Discriminant Splitting Portraits

## Abstract

Binary quadratic forms with equal discriminants have identical splitting symbols at every index.

**Theorem 1.1 (Equal discriminants have equal splitting portraits).**

$$\begin{aligned}\forall Q, Qprime: BinaryQuadraticForm,\\\operatorname{discriminant}(Q) = \operatorname{discriminant}(Qprime) \Rightarrow\\\forall p \in \mathbb{N},\\\operatorname{jacobiSym}(\operatorname{discriminant}(Q), p) = \operatorname{jacobiSym}(\operatorname{discriminant}(Qprime), p).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/EqualDiscriminantSplittingPortrait.equal_discriminant_splitting_portrait` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The form carrier and discriminant are the canonical integer binary quadratic-form objects from the PrimeForms family. No parallel form or discriminant representation is introduced.

At index p, the splitting readout is constructed by applying the Jacobi symbol to the form's discriminant. At prime p this is the Legendre symbol used by the source splitting observer.

Equal discriminants remain equal after applying this same readout at every natural index, so the entire splitting portrait is unable to distinguish the two forms.

## References

- Truth anchor: `D5/S3/PrimeForms/Splitting/EqualDiscriminantSplittingPortrait.equal_discriminant_splitting_portrait`
- Dependency: [D5/S3/PrimeForms/EisensteinDiscriminant](../EisensteinDiscriminant.md)
