# Cyclic Insertion Gaps

> External author-formula rendering through the actual Scribe LatexWriter. Canonical declaration resolution, emission and acceptance are pending.

Deleting a new label from an oriented circular word classifies all possible insertions by a unique actual gap.

Let A be any type with decidable equality, B a nonempty list with no repeated labels, and x a label absent from B. Circular words identify lists under rotation and retain orientation. For j in Fin(length(B)), gapCircle(B,x,j) is the rotation class of x followed by rotate(B,j). Thus j records the gap immediately before the jth entry of B. Deleting x filters it from the circular word. No walk, chosen component or restriction to some gaps is assumed.

## Every Oriented Insertion Has Exactly One Gap

Describe: `complete-deletion-fiber`

$$\forall A \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(A\right)] \forall B \in \mathrm{List}\left(A\right),\; \forall x \in A,\; \forall C \in \mathrm{Cycle}\left(A\right),\; ((\mathrm{Nodup}\left(B\right)) \land ((\neg (B = \mathrm{nil})) \land (\neg (x \in B)))) \Rightarrow (((\mathrm{Nodup}\left(C\right)) \land ((x \in C) \land (\mathrm{delete}\left(x, C\right) = \mathrm{coeCycle}\left(B\right)))) \Leftrightarrow (\exists j \in \mathrm{Fin}\left(\mathrm{length}\left(B\right)\right),\; (C = \mathrm{gapCircle}\left(B, x, j\right)) \land (\forall k \in \mathrm{Fin}\left(\mathrm{length}\left(B\right)\right),\; (C = \mathrm{gapCircle}\left(B, x, k\right)) \Rightarrow (k = j))))$$

An oriented circular word C has distinct labels, contains x and has deletion residual B if and only if C equals gapCircle(B,x,j) for exactly one j. To obtain the gap, rotate a representative of C until x is first. Removing x leaves a rotation of B. Uniqueness uses the fact that x appears once: two representatives beginning with x cannot differ by a nonzero rotation. The remaining lists are therefore equal, and rotation indices of a nonempty list with distinct labels are equal modulo its length. Conversely, every displayed insertion has distinct labels, contains x and deletes to B.

In a construction that deletes several selected labels from an actual permutation, apply this result to the oriented circular word after the earlier deletions. It classifies every child base by the newly selected label's actual gap, so vertex-domain coverage can be established before constructing paths. A reversed residual must be treated with its own orientation. The result does not prove a Hamilton cycle or any endpoint pairing.

