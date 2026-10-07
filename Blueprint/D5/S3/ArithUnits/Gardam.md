# Gardam's Unit-Conjecture Counterexample

## Abstract

Gardam's exact Promislow group-ring counterexample over ZMod 2, transported through a faithful four-coset model.

**Theorem 1.1 (The presented group is torsion-free).**

$$\forall g \in P,\quad \forall n \in \mathbb{N},\quad n \neq 0 \land g^{n} = 1 \Rightarrow g = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/Gardam.presented_torsion_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giles Gardam (2021). *A counterexample to the unit conjecture for group rings*. DOI: [10.4007/annals.2021.194.3.9](https://doi.org/10.4007/annals.2021.194.3.9). URL: <https://arxiv.org/abs/2102.11818v2>.

*Commentary.*

For the exact two-generator presentation from Gardam's Theorem A, every nonzero natural power that equals one forces the element to be one. The proof constructs and verifies a faithful four-coset normal form.

This is the original-P supplier used by the final exact statement. The normal-form group, its action and factor set, and both inverse identities are retained in the Lean dependency path.

**Theorem 1.2 (The official group-ring element is a unit).**

$$\operatorname{IsUnit} u$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/Gardam.official_isUnit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giles Gardam (2021). *A counterexample to the unit conjecture for group rings*. DOI: [10.4007/annals.2021.194.3.9](https://doi.org/10.4007/annals.2021.194.3.9). URL: <https://arxiv.org/abs/2102.11818v2>.

*Commentary.*

The exact element u in the group ring F₂[P] is a unit. The certificate supplies an explicit inverse and checks both left and right products coefficient by coefficient in the four-coset model.

**Theorem 1.3 (The unit is not a group basis element).**

$$\neg \exists g \in P,\quad u = g$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/Gardam.official_not_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giles Gardam (2021). *A counterexample to the unit conjecture for group rings*. DOI: [10.4007/annals.2021.194.3.9](https://doi.org/10.4007/annals.2021.194.3.9). URL: <https://arxiv.org/abs/2102.11818v2>.

*Commentary.*

No element of P equals u. Transport to the faithful normal form reduces this to the explicit 21-element support computation, so the nontrivial unit conclusion remains tied to the original presentation.

**Theorem 1.4 (The explicit inverse works on both sides).**

$$unitE \times inverseE = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/Gardam.mul_inverseE` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giles Gardam (2021). *A counterexample to the unit conjecture for group rings*. DOI: [10.4007/annals.2021.194.3.9](https://doi.org/10.4007/annals.2021.194.3.9). URL: <https://arxiv.org/abs/2102.11818v2>.

*Commentary.*

The four-coset certificate proves unitE * inverseE = 1; the companion inverseE_mul declaration proves the reverse product. These identities are consumed by official_isUnit.

## References

- Truth anchor: `D5/S3/ArithUnits/Gardam.mul_inverseE`
- Truth anchor: `D5/S3/ArithUnits/Gardam.official_isUnit`
- Truth anchor: `D5/S3/ArithUnits/Gardam.official_not_basis`
- Truth anchor: `D5/S3/ArithUnits/Gardam.presented_torsion_free`
