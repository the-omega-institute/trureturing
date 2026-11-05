# SolidResolvingTournamentProfiles

## Abstract

SolidResolvingTournamentProfiles

**Theorem 1.1 (card le of chain cover).**

$$\forall U \in Type,\; \forall P \in Type,\; [\operatorname{Fintype}\left(U\right)] [\operatorname{Preorder}\left(P\right)] \forall f \in \left(U\right) \to \left(P\right),\; \forall m \in \operatorname{Nat},\; \forall chains \in \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{Set}\left(P\right)\right),\; \left(\forall u \in U,\; \exists i \in \operatorname{Fin}\left(m\right),\; \left(f\right)\left(u\right) \in \left(chains\right)\left(i\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(m\right),\; \forall a \in P,\; \forall b \in P,\; a \in \left(chains\right)\left(i\right) \Rightarrow \left(b \in \left(chains\right)\left(i\right) \Rightarrow \left(a \le b \lor b \le a\right)\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.card_le_of_chain_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assigning an incomparable element to a chain containing its image is injective. Therefore the number of elements is at most the number of covering chains.

**Theorem 1.2 (profile finite bound).**

$$\forall k \in \operatorname{Nat},\; \forall R \in \operatorname{Nat},\; \forall D \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \left(D\right)\left(i, j\right) \le R\right) \Rightarrow \left(\operatorname{Fin}\left(k\right)\right) \to \left(\forall x \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{ENat}\right),\; \left(\forall j \in \operatorname{Fin}\left(k\right),\; \exists i \in \operatorname{Fin}\left(k\right),\; \left(x\right)\left(i\right) < \left(fun \left(i: \operatorname{Fin}\left(k\right)\right) \mapsto fun \left(j: \operatorname{Fin}\left(k\right)\right) \mapsto \left(\left(D\right)\left(i, j\right) : \operatorname{ENat}\right)\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \left(x\right)\left(i\right) \le \left(fun \left(i: \operatorname{Fin}\left(k\right)\right) \mapsto fun \left(j: \operatorname{Fin}\left(k\right)\right) \mapsto \left(\left(D\right)\left(i, j\right) : \operatorname{ENat}\right)\right)\left(i, j\right) + \left(x\right)\left(j\right)\right) \Rightarrow \left(\exists y \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Nat}\right),\; \left(\forall i \in \operatorname{Fin}\left(k\right),\; \left(\left(y\right)\left(i\right) : \operatorname{ENat}\right) = \left(x\right)\left(i\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(k\right),\; \left(y\right)\left(i\right) \le 2 \cdot R - 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.profile_finite_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One strict column inequality makes one coordinate finite; the triangle inequalities then make every coordinate finite and at most twice R minus one.

**Definition 1.3 (D32).**

$$\left(D32 : \left(\operatorname{Fin}\left(3\right)\right) \to \left(\left(\operatorname{Fin}\left(3\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 2, 1], ![1, 0, 2], ![2, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D32` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.4 (nat profile bound 3 2).**

$$\forall x \in \left(\operatorname{Fin}\left(3\right)\right) \to \left(\operatorname{Nat}\right),\; \left(\forall i \in \operatorname{Fin}\left(3\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(3\right),\; \exists i \in \operatorname{Fin}\left(3\right),\; \left(x\right)\left(i\right) < \left(D32\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(3\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \left(x\right)\left(i\right) \le \left(D32\right)\left(i, j\right) + \left(x\right)\left(j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(3\right),\; \left(x\right)\left(i\right) \le 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_3_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.5 (D44).**

$$\left(D44 : \left(\operatorname{Fin}\left(4\right)\right) \to \left(\left(\operatorname{Fin}\left(4\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 2, 2, 1], ![1, 0, 3, 2], ![1, 1, 0, 2], ![2, 1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D44` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.6 (nat profile bound 4 4).**

$$\forall x \in \left(\operatorname{Fin}\left(4\right)\right) \to \left(\operatorname{Nat}\right),\; \left(\forall i \in \operatorname{Fin}\left(4\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(4\right),\; \exists i \in \operatorname{Fin}\left(4\right),\; \left(x\right)\left(i\right) < \left(D44\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \left(x\right)\left(i\right) \le \left(D44\right)\left(i, j\right) + \left(x\right)\left(j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(4\right),\; \left(x\right)\left(i\right) \le 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_4_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.7 (D58).**

$$\left(D58 : \left(\operatorname{Fin}\left(5\right)\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 2, 2, 2, 1], ![1, 0, 3, 3, 2], ![1, 1, 0, 3, 2], ![1, 1, 1, 0, 2], ![2, 1, 1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D58` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.8 (nat profile bound 5 8).**

$$\forall x \in \left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right),\; \left(\forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) < \left(D58\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le \left(D58\right)\left(i, j\right) + \left(x\right)\left(j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_8` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.9 (D510).**

$$\left(D510 : \left(\operatorname{Fin}\left(5\right)\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 2, 1, 2, 1], ![1, 0, 2, 3, 2], ![2, 1, 0, 4, 3], ![1, 1, 1, 0, 2], ![2, 1, 1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D510` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.10 (nat profile bound 5 10).**

$$\forall x \in \left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right),\; \left(\forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) < \left(D510\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le \left(D510\right)\left(i, j\right) + \left(x\right)\left(j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_10` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.11 (D512).**

$$\left(D512 : \left(\operatorname{Fin}\left(5\right)\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 2, 2, 1, 1], ![1, 0, 3, 2, 2], ![1, 1, 0, 2, 2], ![2, 1, 1, 0, 3], ![2, 1, 1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D512` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.12 (nat profile bound 5 12).**

$$\forall x \in \left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right),\; \left(\forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) < \left(D512\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le \left(D512\right)\left(i, j\right) + \left(x\right)\left(j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_12` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.13 (D540).**

$$\left(D540 : \left(\operatorname{Fin}\left(5\right)\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 2, 2, 2, 1], ![1, 0, 2, 1, 2], ![1, 1, 0, 2, 2], ![1, 2, 1, 0, 2], ![2, 1, 1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D540` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.14 (nat profile bound 5 40).**

$$\forall x \in \left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right),\; \left(\forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) < \left(D540\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le \left(D540\right)\left(i, j\right) + \left(x\right)\left(j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_40` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.15 (D541).**

$$\left(D541 : \left(\operatorname{Fin}\left(5\right)\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 1, 2, 2, 1], ![2, 0, 2, 1, 3], ![1, 1, 0, 2, 2], ![1, 2, 1, 0, 2], ![2, 1, 1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D541` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.16 (nat profile bound 5 41).**

$$\forall x \in \left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right),\; \left(\forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) < \left(D541\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le \left(D541\right)\left(i, j\right) + \left(x\right)\left(j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_41` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.17 (D576).**

$$\left(D576 : \left(\operatorname{Fin}\left(5\right)\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 2, 2, 1, 1], ![1, 0, 2, 2, 1], ![1, 1, 0, 2, 2], ![2, 1, 1, 0, 2], ![2, 2, 1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D576` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.18 (nat profile bound 5 76).**

$$\forall x \in \left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right),\; \left(\forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) < \left(D576\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le \left(D576\right)\left(i, j\right) + \left(x\right)\left(j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_76` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.19 (acBool).**

$$\forall k \in \operatorname{Nat},\; \forall b \in \operatorname{Nat},\; \forall D \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \forall x \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Fin}\left(b\right)\right),\; \operatorname{acBool}\left(D, x\right) = \operatorname{Bool}.\operatorname{and}\left(\operatorname{Bool}.\operatorname{and}\left(\operatorname{List}.\operatorname{all}\left(\operatorname{List}.\operatorname{finRange}\left(k\right), fun \left(i: \operatorname{Fin}\left(k\right)\right) \mapsto \operatorname{decide}\left(1 \le \operatorname{val}\left(\left(x\right)\left(i\right)\right)\right)\right), \operatorname{List}.\operatorname{all}\left(\operatorname{List}.\operatorname{finRange}\left(k\right), fun \left(j: \operatorname{Fin}\left(k\right)\right) \mapsto \operatorname{List}.\operatorname{any}\left(\operatorname{List}.\operatorname{finRange}\left(k\right), fun \left(i: \operatorname{Fin}\left(k\right)\right) \mapsto \operatorname{decide}\left(\operatorname{val}\left(\left(x\right)\left(i\right)\right) < \left(D\right)\left(i, j\right)\right)\right)\right)\right), \operatorname{List}.\operatorname{all}\left(\operatorname{List}.\operatorname{finRange}\left(k\right), fun \left(i: \operatorname{Fin}\left(k\right)\right) \mapsto \operatorname{List}.\operatorname{all}\left(\operatorname{List}.\operatorname{finRange}\left(k\right), fun \left(j: \operatorname{Fin}\left(k\right)\right) \mapsto \operatorname{decide}\left(\operatorname{val}\left(\left(x\right)\left(i\right)\right) \le \left(D\right)\left(i, j\right) + \operatorname{val}\left(\left(x\right)\left(j\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.acBool` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean test is the conjunction of positivity, a strict comparison in every landmark column, and every triangle upper bound.

**Theorem 1.20 (profile mem of certificate).**

$$\forall k \in \operatorname{Nat},\; \forall D \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \forall ps \in \operatorname{List}\left(\left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Fin}\left(3\right)\right)\right),\; \operatorname{List}.\operatorname{all}\left(\operatorname{enumTuple}\left(\operatorname{List}.\operatorname{finRange}\left(3\right), k\right), fun \left(x: \left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Fin}\left(3\right)\right)\right) \mapsto \operatorname{Bool}.\operatorname{or}\left(\operatorname{Bool}.\operatorname{not}\left(\operatorname{acBool}\left(D, x\right)\right), \operatorname{decide}\left(x \in ps\right)\right)\right) = true \Rightarrow \left(\forall y \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Nat}\right),\; \left(\forall i \in \operatorname{Fin}\left(k\right),\; \left(y\right)\left(i\right) < 3\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(k\right),\; 1 \le \left(y\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(k\right),\; \exists i \in \operatorname{Fin}\left(k\right),\; \left(y\right)\left(i\right) < \left(D\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \left(y\right)\left(i\right) \le \left(D\right)\left(i, j\right) + \left(y\right)\left(j\right)\right) \Rightarrow \left(\exists x \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Fin}\left(3\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{val}\left(\left(x\right)\left(i\right)\right) = \left(y\right)\left(i\right)\right) \land x \in ps\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.profile_mem_of_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A certificate listing all bounded positive profiles supplies a listed Fin-valued representative of every natural profile satisfying the same inequalities.

**Theorem 1.21 (cardinal le profile chains).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall k \in \operatorname{Nat},\; \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \forall chains \in \operatorname{List}\left(\operatorname{List}\left(\left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Fin}\left(3\right)\right)\right)\right),\; \left(\forall u \in U,\; \exists z \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Fin}\left(3\right)\right),\; \left(\forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{val}\left(\left(z\right)\left(j\right)\right) = \left(f\right)\left(u, j\right)\right) \land z \in \operatorname{List}.\operatorname{flatten}\left(chains\right)\right) \Rightarrow \left(\left(\forall ch \in \operatorname{List}\left(\left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Fin}\left(3\right)\right)\right),\; ch \in chains \Rightarrow \left(\forall a \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Fin}\left(3\right)\right),\; a \in ch \Rightarrow \left(\forall b \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Fin}\left(3\right)\right),\; b \in ch \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{val}\left(\left(a\right)\left(j\right)\right) \le \operatorname{val}\left(\left(b\right)\left(j\right)\right)\right) \lor \left(\forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{val}\left(\left(b\right)\left(j\right)\right) \le \operatorname{val}\left(\left(a\right)\left(j\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le \operatorname{List}.\operatorname{length}\left(chains\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.cardinal_le_profile_chains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite list of chains covering the natural profiles bounds the cardinality of any mutually incomparable family of those profiles.

**Theorem 1.22 (strong profile antichain bound 3 2).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(3\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(3\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(3\right),\; \exists i \in \operatorname{Fin}\left(3\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(D32\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(3\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(D32\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_3_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.23 (strong profile antichain bound 4 4).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(4\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(4\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(4\right),\; \exists i \in \operatorname{Fin}\left(4\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(D44\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(D44\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_4_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.24 (strong profile antichain bound 5 8).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(D58\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(D58\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 5\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_8` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.25 (strong profile antichain bound 5 10).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(D510\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(D510\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 5\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_10` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.26 (strong profile antichain bound 5 12).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(D512\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(D512\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 5\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_12` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.27 (strong profile antichain bound 5 40).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(D540\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(D540\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 5\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_40` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.28 (strong profile antichain bound 5 41).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(D541\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(D541\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 5\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_41` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.29 (strong profile antichain bound 5 76).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(D576\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(D576\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 5\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_76` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D32`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D44`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D510`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D512`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D540`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D541`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D576`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.D58`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.acBool`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.card_le_of_chain_cover`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.cardinal_le_profile_chains`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_3_2`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_4_4`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_10`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_12`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_40`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_41`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_76`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.nat_profile_bound_5_8`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.profile_finite_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.profile_mem_of_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_3_2`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_4_4`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_10`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_12`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_40`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_41`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_76`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles.strong_profile_antichain_bound_5_8`
- Dependency: [D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport](../../../ObserverMemory/Algorithms/UniformDescriptorSupport.md)
