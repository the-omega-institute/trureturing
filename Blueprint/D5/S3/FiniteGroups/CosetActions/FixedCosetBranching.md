# Support and cardinality of fixed left cosets

## Abstract

Fixed left cosets are supported on conjugacy classes meeting the subgroup. Two counts of their representatives give the weighted cardinality identity.

Let G be a group, K a subgroup, and g an element of G. Write X for the left cosets in G/K fixed by left multiplication by g, Y for the intersection of the conjugacy class of g with K, and C for the centralizer of g in G.

**Theorem 1.1 (Nonempty support).**

$$X \neq \emptyset \Leftrightarrow Y \neq \emptyset$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CosetActions/FixedCosetBranching.fixedCosets_nonempty_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No finiteness assumption is needed. The representatives whose inverse conjugation sends g into K map onto both X and Y.

**Theorem 1.2 (Cardinality for finite G).**

$$\lvert X \rvert \cdot \lvert K \rvert = \lvert C \rvert \cdot \lvert Y \rvert$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CosetActions/FixedCosetBranching.card_fixedCosets_mul_card_subgroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume G is finite. Over a fixed coset with representative x, the quotient fiber is xK. Over the conjugate given by x, the conjugation fiber is Cx. The two fiber counts give the displayed equation.

In Davydov and Simmons, On Lagrangian algebras in group-theoretical modular categories, use K for the paper's H. In equation (25) the degree-g summand for xK comes from degree x inverse times g times x of the twisted group algebra of K. It is one-dimensional when that conjugate belongs to K and zero otherwise. Equivalently, Theorem 4.8 evaluated at degree g and acting element 1 counts X, since each contributing term is 1. The passage from the categorical algebra to a VOA extension uses an external correspondence. https://arxiv.org/abs/1603.04650

## References

- Truth anchor: `D5/S3/FiniteGroups/CosetActions/FixedCosetBranching.card_fixedCosets_mul_card_subgroup`
- Truth anchor: `D5/S3/FiniteGroups/CosetActions/FixedCosetBranching.fixedCosets_nonempty_iff`
