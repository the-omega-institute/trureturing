# Actual Active Support of Zigzag Choices

## Abstract

For every parameter t at least two, the actual edge support of a native balanced labelled zigzag choice has at most two weak components.

The objects are the native Choices t: one labelled form for each class from 2 through 3t-2, with class two restricted to II, III, IV, and V. The endpoint formulas are those of Feldman's The Missing Zigzag (arXiv:2609.26114v1), Section 5 equation (2). Balance is the existing integer outdegree minus indegree condition at each nonzero residue. The support statements below are derived from these objects; they impose no closure condition and identify no choices under reflection or rotation.

**Definition 1.1 (Endpoints of selected class edges).**

Lean statement: `D5/S3/Combinatorics/Zigzag/ActiveSupport.Active`

*Formalization.* `D5/S3/Combinatorics/Zigzag/ActiveSupport.Active` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A residue is active exactly when it is an endpoint of a selected formPair. The original finite class index is the witness. ActiveVertex is the subtype of these residues, so unused vertices are absent.

**Definition 1.2 (Weak components of actual support).**

Lean statement: `D5/S3/Combinatorics/Zigzag/ActiveSupport.ActiveComponent`

*Formalization.* `D5/S3/Combinatorics/Zigzag/ActiveSupport.ActiveComponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SupportArrow has precisely the selected directed endpoint pairs, witnessed by their class labels. Its equivalence closure forgets orientation for reachability. Restricting that equivalence to ActiveVertex and taking the quotient gives the actual weak components. This equivalence identifies vertices, never the underlying labelled choices.

**Theorem 1.3 (At most two actual active components).**

$$\forall t \in \mathbb{N},\; 2 \le t \Rightarrow \left(\forall c \in \mathrm{Choices}\left(t\right),\; \mathrm{Balanced}\left(c\right) \Rightarrow \mathrm{activeComponentCount}\left(c\right) \le 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/ActiveSupport.active_component_count_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every t at least two and every native balanced choice c, the natural cardinality of ActiveComponent c is at most two. The native complete parity correspondences express c as a signed retirement path. Every endpoint of the starting edge reaches a semitone vertex. Each subsequent pair attaches to a semitone or to an already anchored frontier with nonzero charge. Both the even antipodal pair and the odd singleton preserve anchoring. Hence every actual component contains an actually used semitone. The subtype of used semitones, which may have only one element, surjects onto the component quotient and has cardinality at most two.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/ActiveSupport.Active`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/ActiveSupport.ActiveComponent`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/ActiveSupport.active_component_count_le_two`
- Dependency: [D5/S3/Combinatorics/Zigzag/EvenPaths](EvenPaths.md)
- Dependency: [D5/S3/Combinatorics/Zigzag/OddPaths](OddPaths.md)
