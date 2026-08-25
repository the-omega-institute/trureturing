# The Quotient Universal Property of the Ideal Class Group

## Abstract

A group homomorphism on invertible fractional ideals that is trivial on every principal ideal descends uniquely through the canonical class-group map.

**Theorem 1.1 (Principal-trivial homomorphisms factor uniquely through ideal classes).**

$$\forall R, H, f,\\{}\operatorname{CommRing}\left(R\right) \land \operatorname{IsDedekindDomain}\left(R\right) \land \operatorname{Group}\left(H\right) \land f: \operatorname{GroupHom}\left(\operatorname{Units}\left(\operatorname{FractionalIdeal}\left(R, \operatorname{FractionRing}\left(R\right)\right)\right), H\right) \land (\forall x: \operatorname{Units}\left(\operatorname{FractionRing}\left(R\right)\right), f(\operatorname{toPrincipalIdeal}\left(R, \operatorname{FractionRing}\left(R\right), x\right)) = 1) \Rightarrow\\{}\exists! f': \operatorname{GroupHom}\left(\operatorname{ClassGroup}\left(R\right), H\right), f = f' \circ \operatorname{ClassGroupMk}\left(R\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/ClassGroupQuotientUniversality.class_group_quotient_universality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the group of invertible fractional ideals of a Dedekind domain in its canonical fraction ring. Principal ideals are the image of Mathlib's canonical toPrincipalIdeal homomorphism, and ClassGroup.mk is the displayed quotient projection.

The hypothesis puts the entire principal-ideal subgroup in the kernel of f. Mathlib's quotient lift then constructs the descended group homomorphism and supplies its computation rule. Surjectivity of the canonical quotient projection forces any second factor to agree on every ideal class, proving the displayed uniqueness.

This is the quotient universal property itself. It does not choose a generator for a principal ideal and does not replace the class group with an auxiliary quotient. It closes atom generic-residual-18593e23e5f9dbe82590a77864f09745c0c9f00aaedb5e66c2f7b77a428cdd27.

## References

- Truth anchor: `D5/S3/Factorization/IdealClassGroups/ClassGroupQuotientUniversality.class_group_quotient_universality`
