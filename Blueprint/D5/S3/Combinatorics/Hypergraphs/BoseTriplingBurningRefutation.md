# Ordinary burning under Bose tripling

## Abstract

The cyclic Steiner triple system of order 13 has ordinary burning number 5. Its Bose tripling has burning number 6.

**Definition 1.1 (Bose tripling implication).**

$$\operatorname{claim} \Leftrightarrow (\forall n \in \operatorname{Nat},\; \forall H \in \operatorname{Steiner}\left(\operatorname{Fin}\left(n\right)\right),\; 0 < n \Rightarrow \left(\operatorname{Nondegenerate}\left(H\right) \Rightarrow \left(\operatorname{burning}\left(H\right) < \operatorname{burning}\left(\operatorname{bose}\left(H\right)\right) \Rightarrow (\operatorname{Projective}\left(H\right) \lor \operatorname{Affine}\left(H\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/BoseTriplingBurningRefutation.claim` (`✓ std3`).

*Citation.* Andrea C. Burgess, Peter H. Danziger, Caleb W. Jones, Trent G. Marbach, and David A. Pike (2026). *Burning Steiner Triple Systems*. URL: <https://arxiv.org/html/2608.25627v1>.

*Commentary.*

Section 5 asks whether only the stated geometric families can have increased ordinary burning number under doubling or tripling. This implication takes the tripling part with the cited Bose operation. Its blocks on pairs (x,i) are the vertical triples and the triples formed by (x,i), (y,i), and (complete(x,y),i+1) for distinct x and y, with layers modulo 3. In each ordinary round the source is absent from the preceding burned set, and propagation completes pairs from that set. Non-degeneracy quantifies over every inclusion-maximal nonempty proper subsystem.

**Theorem 1.2 (An order-13 counterexample).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hypergraphs/BoseTriplingBurningRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/burgess-et-al-2026-bose-tripling-burning` (refuted) by `D5/S3/Combinatorics/Hypergraphs/BoseTriplingBurningRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"burgess-et-al-2026-bose-tripling-burning","declaration_gid":"D5/S3/Combinatorics/Hypergraphs/BoseTriplingBurningRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Andrea C. Burgess, Peter H. Danziger, Caleb W. Jones, Trent G. Marbach, and David A. Pike (2026). *Burning Steiner Triple Systems*. URL: <https://arxiv.org/html/2608.25627v1>.

*Commentary.*

Use the translates modulo 13 of the triples {0,1,4} and {0,2,7}. Every nonblock triple generates the base system, so each maximal proper subsystem is a block. The base has lazy burning number 3 and every block has lazy burning number 2. The certified ordinary schedules have lengths 5 and 6. At most 8 points burn in four rounds, and counting pairs in the preceding burned set gives at most 37 in five rounds. Order 13 lies strictly between consecutive admissible orders in each geometric family, namely 7 and 15 for projective systems and 9 and 27 for affine systems.

## References

- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/BoseTriplingBurningRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/BoseTriplingBurningRefutation.result`
