# SolidResolvingTournamentTerminal

## Abstract

SolidResolvingTournamentTerminal

**Definition 1.1 (upperOfCode).**

$$\forall I \in Type,\; \forall D \in \left(I\right) \to \left(\left(I\right) \to \left(\operatorname{Nat}\right)\right),\; \forall i \in I,\; \forall j \in I,\; \operatorname{upperOfCode}\left(D, i, j\right) = \operatorname{ite}\left(\left(D\right)\left(i, j\right) = 8, \infty, \left(\left(D\right)\left(i, j\right) : \operatorname{ENat}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.upperOfCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural code eight represents infinity. Every other code is its natural-number cast into ENat.

**Definition 1.2 (nonD30).**

$$\left(nonD30 : \left(\operatorname{Fin}\left(3\right)\right) \to \left(\left(\operatorname{Fin}\left(3\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 8, 8], ![1, 0, 8], ![1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD30` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.3 (nonstrong profile bound 3 0).**

$$\forall x \in \left(\operatorname{Fin}\left(3\right)\right) \to \left(\operatorname{ENat}\right),\; \left(\forall i \in \operatorname{Fin}\left(3\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(3\right),\; \exists i \in \operatorname{Fin}\left(3\right),\; \left(x\right)\left(i\right) < \left(\operatorname{upperOfCode}\left(nonD30\right)\right)\left(i, j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(3\right),\; \left(x\right)\left(i\right) \le 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_3_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.4 (nonD40).**

$$\left(nonD40 : \left(\operatorname{Fin}\left(4\right)\right) \to \left(\left(\operatorname{Fin}\left(4\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 8, 8, 8], ![1, 0, 8, 8], ![1, 1, 0, 8], ![1, 1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD40` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.5 (nonstrong profile bound 4 0).**

$$\forall x \in \left(\operatorname{Fin}\left(4\right)\right) \to \left(\operatorname{ENat}\right),\; \left(\forall i \in \operatorname{Fin}\left(4\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(4\right),\; \exists i \in \operatorname{Fin}\left(4\right),\; \left(x\right)\left(i\right) < \left(\operatorname{upperOfCode}\left(nonD40\right)\right)\left(i, j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(4\right),\; \left(x\right)\left(i\right) \le 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_4_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.6 (nonD42).**

$$\left(nonD42 : \left(\operatorname{Fin}\left(4\right)\right) \to \left(\left(\operatorname{Fin}\left(4\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 2, 1, 8], ![1, 0, 2, 8], ![2, 1, 0, 8], ![1, 1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD42` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.7 (nonstrong profile bound 4 2).**

$$\forall x \in \left(\operatorname{Fin}\left(4\right)\right) \to \left(\operatorname{ENat}\right),\; \left(\forall i \in \operatorname{Fin}\left(4\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(4\right),\; \exists i \in \operatorname{Fin}\left(4\right),\; \left(x\right)\left(i\right) < \left(\operatorname{upperOfCode}\left(nonD42\right)\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \left(x\right)\left(i\right) \le \left(\operatorname{upperOfCode}\left(nonD42\right)\right)\left(i, j\right) + \left(x\right)\left(j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(4\right),\; \left(x\right)\left(i\right) \le 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_4_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.8 (nonD45).**

$$\left(nonD45 : \left(\operatorname{Fin}\left(4\right)\right) \to \left(\left(\operatorname{Fin}\left(4\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 1, 2, 1], ![8, 0, 8, 8], ![1, 1, 0, 2], ![2, 1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD45` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.9 (nonstrong profile bound 4 5).**

$$\forall x \in \left(\operatorname{Fin}\left(4\right)\right) \to \left(\operatorname{ENat}\right),\; \left(\forall i \in \operatorname{Fin}\left(4\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(4\right),\; \exists i \in \operatorname{Fin}\left(4\right),\; \left(x\right)\left(i\right) < \left(\operatorname{upperOfCode}\left(nonD45\right)\right)\left(i, j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(4\right),\; \left(x\right)\left(i\right) \le 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_4_5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.10 (nonD50).**

$$\left(nonD50 : \left(\operatorname{Fin}\left(5\right)\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 8, 8, 8, 8], ![1, 0, 8, 8, 8], ![1, 1, 0, 8, 8], ![1, 1, 1, 0, 8], ![1, 1, 1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD50` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.11 (nonstrong profile bound 5 0).**

$$\forall x \in \left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{ENat}\right),\; \left(\forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) < \left(\operatorname{upperOfCode}\left(nonD50\right)\right)\left(i, j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.12 (nonD52).**

$$\left(nonD52 : \left(\operatorname{Fin}\left(5\right)\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 2, 1, 8, 8], ![1, 0, 2, 8, 8], ![2, 1, 0, 8, 8], ![1, 1, 1, 0, 8], ![1, 1, 1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD52` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.13 (nonstrong profile bound 5 2).**

$$\forall x \in \left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{ENat}\right),\; \left(\forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) < \left(\operatorname{upperOfCode}\left(nonD52\right)\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le \left(\operatorname{upperOfCode}\left(nonD52\right)\right)\left(i, j\right) + \left(x\right)\left(j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.14 (nonD54).**

$$\left(nonD54 : \left(\operatorname{Fin}\left(5\right)\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 2, 2, 1, 8], ![1, 0, 3, 2, 8], ![1, 1, 0, 2, 8], ![2, 1, 1, 0, 8], ![1, 1, 1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD54` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.15 (nonstrong profile bound 5 4).**

$$\forall x \in \left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{ENat}\right),\; \left(\forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) < \left(\operatorname{upperOfCode}\left(nonD54\right)\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le \left(\operatorname{upperOfCode}\left(nonD54\right)\right)\left(i, j\right) + \left(x\right)\left(j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.16 (nonD55).**

$$\left(nonD55 : \left(\operatorname{Fin}\left(5\right)\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 1, 2, 1, 8], ![8, 0, 8, 8, 8], ![1, 1, 0, 2, 8], ![2, 1, 1, 0, 8], ![1, 1, 1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD55` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.17 (nonstrong profile bound 5 5).**

$$\forall x \in \left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{ENat}\right),\; \left(\forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) < \left(\operatorname{upperOfCode}\left(nonD55\right)\right)\left(i, j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.18 (nonD59).**

$$\left(nonD59 : \left(\operatorname{Fin}\left(5\right)\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 1, 2, 2, 1], ![8, 0, 8, 8, 8], ![1, 1, 0, 3, 2], ![1, 1, 1, 0, 2], ![2, 1, 1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD59` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.19 (nonstrong profile bound 5 9).**

$$\forall x \in \left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{ENat}\right),\; \left(\forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) < \left(\operatorname{upperOfCode}\left(nonD59\right)\right)\left(i, j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_9` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Definition 1.20 (nonD511).**

$$\left(nonD511 : \left(\operatorname{Fin}\left(5\right)\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right)\right) = ![![0, 1, 1, 2, 1], ![8, 0, 8, 8, 8], ![8, 1, 0, 8, 8], ![1, 1, 1, 0, 2], ![2, 1, 1, 1, 0]]$$

*Formalization.* `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD511` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed concrete matrix gives directed distance upper-bound codes for the representative landmark tournament. Code eight denotes infinity when upperOfCode is applied.

**Theorem 1.21 (nonstrong profile bound 5 11).**

$$\forall x \in \left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{ENat}\right),\; \left(\forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) < \left(\operatorname{upperOfCode}\left(nonD511\right)\right)\left(i, j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(5\right),\; \left(x\right)\left(i\right) \le 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The necessary inequalities for an outside distance profile force every coordinate to be at most two.

**Theorem 1.22 (nonstrong antichain bound 3 0).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(3\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(3\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le 2\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(3\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(3\right),\; \exists i \in \operatorname{Fin}\left(3\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(nonD30\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(3\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(nonD30\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_3_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.23 (nonstrong antichain bound 4 0).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(4\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(4\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le 2\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(4\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(4\right),\; \exists i \in \operatorname{Fin}\left(4\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(nonD40\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(nonD40\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 2\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_4_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.24 (nonstrong antichain bound 4 2).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(4\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(4\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le 2\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(4\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(4\right),\; \exists i \in \operatorname{Fin}\left(4\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(nonD42\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(nonD42\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 2\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_4_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.25 (nonstrong antichain bound 4 5).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(4\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(4\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le 2\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(4\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(4\right),\; \exists i \in \operatorname{Fin}\left(4\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(nonD45\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(nonD45\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 2\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_4_5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.26 (nonstrong antichain bound 5 0).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le 2\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(nonD50\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(nonD50\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 5\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.27 (nonstrong antichain bound 5 2).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le 2\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(nonD52\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(nonD52\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 5\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.28 (nonstrong antichain bound 5 4).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le 2\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(nonD54\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(nonD54\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 5\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.29 (nonstrong antichain bound 5 5).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le 2\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(nonD55\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(nonD55\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 5\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.30 (nonstrong antichain bound 5 9).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le 2\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(nonD59\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(nonD59\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 5\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_9` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.31 (nonstrong antichain bound 5 11).**

$$\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(5\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le 2\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(5\right),\; \exists i \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(nonD511\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(5\right),\; \forall j \in \operatorname{Fin}\left(5\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(nonD511\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le 5\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite family of positive profiles satisfying the displayed inequalities and mutual incomparability has the stated cardinality bound. The finite chain cover is used after bounding every coordinate by two.

**Theorem 1.32 (strong enat profile bound).**

$$\forall k \in \operatorname{Nat},\; \forall D \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \left(D\right)\left(i, j\right) \le 4\right) \Rightarrow \left(\operatorname{Fin}\left(k\right)\right) \to \left(\left(\forall y \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Nat}\right),\; \left(\forall i \in \operatorname{Fin}\left(k\right),\; 1 \le \left(y\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(k\right),\; \exists i \in \operatorname{Fin}\left(k\right),\; \left(y\right)\left(i\right) < \left(D\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \left(y\right)\left(i\right) \le \left(D\right)\left(i, j\right) + \left(y\right)\left(j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(k\right),\; \left(y\right)\left(i\right) \le 2\right)\right)\right)\right) \Rightarrow \left(\forall x \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{ENat}\right),\; \left(\forall i \in \operatorname{Fin}\left(k\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(k\right),\; \exists i \in \operatorname{Fin}\left(k\right),\; \left(x\right)\left(i\right) < \left(\operatorname{upperOfCode}\left(D\right)\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \left(x\right)\left(i\right) \le \left(\operatorname{upperOfCode}\left(D\right)\right)\left(i, j\right) + \left(x\right)\left(j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(k\right),\; \left(x\right)\left(i\right) \le 2\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.strong_enat_profile_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite landmark upper bounds make the entire extended-natural profile finite. The corresponding natural-profile estimate then bounds every original coordinate by two.

**Theorem 1.33 (card bound of profile model).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall k \in \operatorname{Nat},\; \forall c \in \operatorname{Nat},\; \forall R \in \left(V\right) \to \left(\left(V\right) \to \left(Prop\right)\right),\; \forall L \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(V\right),\; \operatorname{Function}.\operatorname{Injective}\left(L\right) \Rightarrow \left(\operatorname{IsSolidResolving}\left(R, \operatorname{Set}.\operatorname{range}\left(L\right)\right) \Rightarrow \left(\forall D \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \operatorname{directedDistance}\left(R, \left(L\right)\left(i\right), \left(L\right)\left(j\right)\right) \le \operatorname{upperOfCode}\left(D, i, j\right)\right) \Rightarrow \left(\left(\forall x \in \left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{ENat}\right),\; \left(\forall i \in \operatorname{Fin}\left(k\right),\; 1 \le \left(x\right)\left(i\right)\right) \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(k\right),\; \exists i \in \operatorname{Fin}\left(k\right),\; \left(x\right)\left(i\right) < \left(\operatorname{upperOfCode}\left(D\right)\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \left(x\right)\left(i\right) \le \left(\operatorname{upperOfCode}\left(D\right)\right)\left(i, j\right) + \left(x\right)\left(j\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(k\right),\; \left(x\right)\left(i\right) \le 2\right)\right)\right)\right) \Rightarrow \left(\left(\forall U \in Type,\; [\operatorname{Fintype}\left(U\right)] \forall f \in \left(U\right) \to \left(\left(\operatorname{Fin}\left(k\right)\right) \to \left(\operatorname{Nat}\right)\right),\; \left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(k\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le 2\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(k\right),\; 1 \le \left(\left(f\right)\left(u\right)\right)\left(i\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall j \in \operatorname{Fin}\left(k\right),\; \exists i \in \operatorname{Fin}\left(k\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) < \left(D\right)\left(i, j\right)\right) \Rightarrow \left(\left(\forall u \in U,\; \forall i \in \operatorname{Fin}\left(k\right),\; \forall j \in \operatorname{Fin}\left(k\right),\; \left(\left(f\right)\left(u\right)\right)\left(i\right) \le \left(D\right)\left(i, j\right) + \left(\left(f\right)\left(u\right)\right)\left(j\right)\right) \Rightarrow \left(\left(\forall a \in U,\; \forall b \in U,\; a \ne b \Rightarrow \left(\neg \left(\left(f\right)\left(a\right) \le \left(f\right)\left(b\right)\right) \land \neg \left(\left(f\right)\left(b\right) \le \left(f\right)\left(a\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(U\right) \le c\right)\right)\right)\right)\right) \Rightarrow \operatorname{Fintype}.\operatorname{card}\left(V\right) \le k + c\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.card_bound_of_profile_model` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Vertices outside the landmarks have mutually incomparable positive distance profiles. A bound on the cardinality of these profiles adds to the number of landmarks to bound the ambient order.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.card_bound_of_profile_model`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD30`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD40`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD42`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD45`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD50`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD511`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD52`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD54`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD55`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonD59`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_3_0`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_4_0`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_4_2`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_4_5`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_0`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_11`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_2`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_4`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_5`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_antichain_bound_5_9`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_3_0`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_4_0`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_4_2`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_4_5`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_0`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_11`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_2`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_4`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_5`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.nonstrong_profile_bound_5_9`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.strong_enat_profile_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentTerminal.upperOfCode`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase](SolidResolvingTournamentBase.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles](SolidResolvingTournamentProfiles.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport](../../../ObserverMemory/Algorithms/UniformDescriptorSupport.md)
