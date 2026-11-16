# Part II Unitriangular Lang

## Abstract

The height-torus Lang map, its finite inverse and its resonant-root obstruction on Uplus over an arbitrary field.

Let F be any field, n any natural rank and a a unit of F. Uplus n F is the upper-unitriangular subgroup of the determinant-one matrices. Restrict heightTorus(a) to obtain sigma(a), and define psi(a)(g) = sigma(a)(g)*g^-1. Writing g = 1+X and a target y = 1+b, the group equation psi(a)(g) = y is equivalent to sigma(a)(g) = y*g, hence to delta(a)(X) = b + b*X.

Under nonresonance, the strict-upper coordinate solution is the sum of T_b^k(deltaInv(a)(b)) for 0 <= k < n-1, where T_b(X) = deltaInv(a)(b*X). Adding the identity matrix produces langInverse(a)(y) in the same Uplus subgroup. The coordinate equation yields the right inverse law, and coordinate uniqueness yields the left inverse law.

**Theorem 1.1 (psi Lang inverse).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang.psi_langInverse`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang.psi_langInverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual Uplus subgroup, the explicit inverse is a right inverse for the orientation heightTorus a g multiplied by g inverse.

**Theorem 1.2 (Lang inverse psi).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang.langInverse_psi`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang.langInverse_psi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same explicit construction is a left inverse on the actual Uplus subgroup, using strict-upper uniqueness.

**Theorem 1.3 (resonant transvection obstruction).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang.resonant_transvection_not_range`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang.resonant_transvection_not_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When a positive root weight vanishes, the explicit transvection at that root is outside the range; the obstruction uses the actual matrix entry and no cardinality assumption.

**Theorem 1.4 (height torus Lang criterion).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang.heightTorus_lang_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang.heightTorus_lang_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the actual Uplus subgroup over any field and every natural rank, surjectivity and bijectivity coincide and are equivalent to nonresonance.

Resonance at a positive distance d means that the root weight a^d-1 is zero. The target transvection 1+E_(0,d) then forces 0 = 1 at entry (0,d): the delta term vanishes, while the product b*X contributes X_(d,d) = 0. Thus this explicit target is unreachable. Nonresonance is equivalent to surjectivity and bijectivity for every rank, including zero and one.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang.heightTorus_lang_criterion`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang.langInverse_psi`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang.psi_langInverse`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang.resonant_transvection_not_range`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularActions](PartIIUnitriangularActions.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLangLinear](PartIIUnitriangularLangLinear.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular](SLnUnitriangular.md)
