# Concrete Remaining Native Star Contacts

## Abstract

The concrete remaining stars are disjoint and each meets the actual two-star core in one full circle whose native b edge survives the core cuts.

For j in Fin(m-2), contactAnchor(j) is the actual permutation tuple (1,...,j+1,m,j+2,...,m-1,0). Thus the finite indices enumerate the literal insertion labels 1 through m-2. SupplierStar(z) fixes the circular residual tuple obtained by deleting z's last label, up to whole reversal. Circle(z) fixes the complete actual tuple up to rotation and reversal. These domains are specified before choosing any path or Hamilton cycle.

**Theorem 1.1 (Distinct Concrete Insertion Stars Are Disjoint).**

$$\forall m \in \mathrm{Nat},\; \forall i \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \left(\neg i = j\right) \Rightarrow \mathrm{Disjoint}\left(\mathrm{starDomain}\left(\mathrm{contactAnchor}\left(i\right)\right), \mathrm{starDomain}\left(\mathrm{contactAnchor}\left(j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarContacts.contact_stars_pairwise_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every contact star deletes 0. In its residual circle the neighbours of m are j+1 and j+2. A common actual configuration would identify the residual cycles either directly or with their orientations reversed. Direct equality forces the two finite indices to agree; reverse equality contradicts the two consecutive neighbour equations. The claim concerns the complete stars.

**Theorem 1.2 (The Lower Supplier Misses Every Remaining Star).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \mathrm{Disjoint}\left(\mathrm{starDomain}\left(\mathrm{contactAnchor}\left(j\right)\right), \mathrm{starDomain}\left(\mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarContacts.contact_star_lower_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least four, the lower a*c supplier also deletes 0, but its residual neighbours of m are 1 and m-1. These cannot equal the consecutive contact neighbours in either orientation. This excludes the full lower star, including both shared core circles.

**Theorem 1.3 (The Upper Supplier Has Exactly the Actual Contact Circle).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \forall v \in \mathrm{Configuration}\left(m\right),\; \left(\mathrm{SupplierStar}\left(\mathrm{contactAnchor}\left(j\right), v\right) \land \mathrm{SupplierStar}\left(\mathrm{mul}\left(\mathrm{swap}\left(0, \mathrm{last}\left(m\right)\right), \mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right)\right), v\right)\right) \Leftrightarrow \mathrm{Circle}\left(\mathrm{contactAnchor}\left(j\right), v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarContacts.contact_star_upper_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal contact tuple is the rotation by m-1-j of upperPort(j). Hence its complete circle is exactly the corresponding upper noncore circle and belongs to its contact star. The existing actual T circle partition places every upper vertex in a lower-owned circle or an upper noncore circle. Lower disjointness excludes the first case, and pairwise star disjointness forces the second circle's owner to be j. Both directions retain the full circle.

**Theorem 1.4 (The Two-Star Core Meets the New Star in One Complete Circle).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \forall v \in \mathrm{Configuration}\left(m\right),\; \left(\mathrm{CoreDomain}\left(m, v\right) \land \mathrm{SupplierStar}\left(\mathrm{contactAnchor}\left(j\right), v\right)\right) \Leftrightarrow \mathrm{Circle}\left(\mathrm{contactAnchor}\left(j\right), v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarContacts.contact_star_core_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CoreDomain is the actual union of the lower a*c and upper tau*a*c deletion stars, where tau swaps labels 0 and m. The lower intersection is empty and the upper intersection is the complete contact circle. This earns the one-contact domain hypothesis required by the existing actual native E grafting theorem.

**Theorem 1.5 (The Actual Contact b Edge Survives the Literal Core Cuts).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \neg \mathrm{CoreDeletedEdge}\left(m, \mathrm{Sym2}\left(\mathrm{contactAnchor}\left(j\right), \mathrm{mul}\left(\mathrm{contactAnchor}\left(j\right), \mathrm{b}\left(m\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarContacts.contact_b_edge_not_deleted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CoreDeletedEdge is the independently specified literal T cut inventory. Both endpoints of every lower-owned cut belong to the lower supplier, which misses the contact star. Both endpoints of every upper cut have last label m, whereas the contact anchor has last label 0. Equality of undirected edges would identify the contact anchor with one of those endpoints and contradict the corresponding invariant. The existing core edge inventory therefore retains this same actual contact edge.

These results classify the concrete remaining graft contacts and their old core edges for every m at least four. They do not assert full second-layer coverage, marked-path recombination, or the all-size recursive Hamiltonicity conclusion; those require their own actual support and edge arguments.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarContacts.contact_b_edge_not_deleted`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarContacts.contact_star_core_intersection`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarContacts.contact_star_lower_disjoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarContacts.contact_star_upper_intersection`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarContacts.contact_stars_pairwise_disjoint`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing](NativeCoreSplicing.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarGrafting](NativeStarGrafting.md)
