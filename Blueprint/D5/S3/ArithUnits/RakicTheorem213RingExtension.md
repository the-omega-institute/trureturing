# Group inverses of differences

## Abstract

Rakić's difference criterion for group inverses extends to unital associative rings.

**Definition 1.1 (Group inverse).**

$$\forall (R: \operatorname{Type}) [\operatorname{Ring}\left(R\right)] (x,y: R), \operatorname{GroupInv}\left(x, y\right) \iff (xyx = x \land \operatorname{FD}\left(x, y\right))$$

*Formalization.* `D5/S3/ArithUnits/RakicTheorem213RingExtension.GroupInv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dragan S. Rakić (2026). *A square analogue of the diamond order and a unified approach to the plus order*. DOI: [10.48550/arXiv.2611.34245](https://doi.org/10.48550/arXiv.2611.34245). URL: <https://arxiv.org/pdf/2611.34245v1#page=11>.

*Commentary.*

A group inverse is a finite Drazin inverse with zero remainder. Equivalently, the two elements satisfy both reflexive inverse equations and commute.

**Definition 1.2 (Minus relation).**

$$\forall (R: \operatorname{Type}) [\operatorname{Ring}\left(R\right)] (a,b: R), \operatorname{MinusOrder}\left(a, b\right) \iff (\exists (u: R), aua = a \land ua = ub \land au = bu)$$

*Formalization.* `D5/S3/ArithUnits/RakicTheorem213RingExtension.MinusOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Dragan S. Rakić (2026). *A square analogue of the diamond order and a unified approach to the plus order*. DOI: [10.48550/arXiv.2611.34245](https://doi.org/10.48550/arXiv.2611.34245). URL: <https://arxiv.org/pdf/2611.34245v1#page=11>.

*Commentary.*

The same inner-inverse witness gives the two equalities comparing the inputs.

**Theorem 1.3 (Rakić's ring extension question).**

$$\forall (R: \operatorname{Type}) [\operatorname{Ring}\left(R\right)] (a,\alpha,b,\beta: R), \operatorname{GroupInv}\left(a, \alpha\right) \to \operatorname{GroupInv}\left(b, \beta\right) \to ((\operatorname{MinusOrder}\left(a, b\right) \land \operatorname{GroupInv}\left(b - a, \beta - \alpha\right)) \iff (a^{3} = aba \land a^{3} = ab^{2} \land a^{3} = b^{2}a \land (b - a)^{3} = b^{3} - a^{3}))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/RakicTheorem213RingExtension.result` (`✓ std3`). ∎

*Resolves.* `Problems/rakic-2026-theorem-2-13-ring-extension` (proved) by `D5/S3/ArithUnits/RakicTheorem213RingExtension.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rakic-2026-theorem-2-13-ring-extension","declaration_gid":"D5/S3/ArithUnits/RakicTheorem213RingExtension.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Dragan S. Rakić (2026). *A square analogue of the diamond order and a unified approach to the plus order*. DOI: [10.48550/arXiv.2611.34245](https://doi.org/10.48550/arXiv.2611.34245). URL: <https://arxiv.org/pdf/2611.34245v1#page=11>.

*Commentary.*

The criterion applies to every unital associative ring, including the zero ring. The witnesses alpha and beta are group inverses of a and b, respectively.

Put p = b beta, e = a alpha and c = b minus a. The minus relation is equivalent to absorption of a by p on both sides and a beta a = a. In that case c beta c = c. The inner inverse equation for the difference forces c alpha c = 0. The outer inverse and commuting equations then imply e b e = a and b squared times e = e times b squared = a squared. These yield the first three cubic identities. Applying the argument to c and its complement a gives the difference-of-cubes identity.

Conversely, the first three identities give the absorption equations and a beta a = a. Expanding the difference-of-cubes identity and multiplying on the left by beta squared gives c alpha c = 0. Substitution yields both inverse equations and commutation for the difference.

## References

- Truth anchor: `D5/S3/ArithUnits/RakicTheorem213RingExtension.GroupInv`
- Truth anchor: `D5/S3/ArithUnits/RakicTheorem213RingExtension.MinusOrder`
- Truth anchor: `D5/S3/ArithUnits/RakicTheorem213RingExtension.result`
- Dependency: [D5/S3/ArithUnits/GolovanovBareDrazinEqualities](GolovanovBareDrazinEqualities.md)
