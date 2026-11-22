# Parking orders and lower Heap sweeps

## Abstract

Ordered lower sweeps and their penultimate net.

**Definition 1.1 (Recovering a physical swap partner).**

$$\forall(\alpha:Type),[\operatorname{DecidableEq}\left(\alpha\right)],\forall(C:\operatorname{Equiv.Perm}\left(\alpha\right)),\forall(\mathit{top}:\alpha),\forall(e:\mathbb{N} \to \alpha),\exists \theta:\mathbb{N} \to \operatorname{Equiv.Perm}\left(\alpha\right),\begin{aligned}\theta\left(0\right) = 1\\\forall(j:\mathbb{N}),\theta\left(j + 1\right) = \operatorname{Equiv.swap}\left(C\left(\theta\left(j\right)\left(e\left(j\right)\right)\right), \mathit{top}\right) \cdot C \cdot \theta\left(j\right)\\\forall(j:\mathbb{N}),\operatorname{parkingPartner}\left(C, \mathit{top}, e, j\right) = C\left(\theta\left(j\right)\left(e\left(j\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.parkingPartner` (`✓ std3`).

*Citation.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Theorem 18(a) uses the block start followed by the lower net. In the formula θ is the sequence of block starts. The current item e(j) is prescribed by the parking order.

**Definition 1.2 (The initial segment of the parking order).**

$$\forall(\alpha:Type),\forall(\mathit{top}:\alpha),\forall(e:\mathbb{N} \to \alpha),\forall(j:\mathbb{N}),\operatorname{path}\left(\mathit{top}, e, j\right) = \mathit{top}::\operatorname{List.ofFn}\left((i:\operatorname{Fin}\left(j\right))\mapsto e\left((i).val\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.path` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

The first entry is the initially parked item. Each later entry is a prescribed item.

**Definition 1.3 (The item at each block start).**

$$\forall(\alpha:Type),\forall(\mathit{top}:\alpha),\forall(e:\mathbb{N} \to \alpha),\forall(j:\mathbb{N}),\begin{aligned}\operatorname{parked}\left(\mathit{top}, e, 0\right) = \mathit{top}\\\operatorname{parked}\left(\mathit{top}, e, j + 1\right) = e\left(j\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.parked` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Index zero is the start before the first scheduled swap.

**Definition 1.4 (Zero-based positions).**

$$\forall(n:\mathbb{N}),[\operatorname{NeZero}\left(n\right)],\forall(i:\mathbb{N}),\operatorname{slot}\left(n, i\right) = \operatorname{Fin.ofNat}\left(n, i\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.slot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Indices are interpreted using the residue modulo the size of the carrier.

**Theorem 1.5 (The value of an in-range position).**

$$\forall(n:\mathbb{N}),[\operatorname{NeZero}\left(n\right)],\forall(i:\mathbb{N}),(i < n)\longrightarrow (\operatorname{slot}\left(n, i\right)).val = i$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.slot_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

An index below the carrier size represents itself.

**Definition 1.6 (The first positions in order).**

$$\forall(n:\mathbb{N}),[\operatorname{NeZero}\left(n\right)],\forall(k:\mathbb{N}),\operatorname{initial}\left(n, k\right) = \operatorname{List.ofFn}\left((i:\operatorname{Fin}\left(k\right))\mapsto \operatorname{slot}\left(n, (i).val\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

The order is increasing in the zero-based indices.

**Theorem 1.7 (A prefix of positions has no repetition).**

$$\forall(n:\mathbb{N}),[\operatorname{NeZero}\left(n\right)],\forall(k:\mathbb{N}),(k \le n)\longrightarrow (\operatorname{initial}\left(n, k\right)).Nodup$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.initial_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Each in-range index identifies a different finite position.

**Definition 1.8 (Cyclic schedule partners).**

$$\forall(n:\mathbb{N}),[\operatorname{NeZero}\left(n\right)],\forall(k:\mathbb{N}),\forall(j:\mathbb{N}),\begin{aligned}(k \operatorname{mod} 2 = 0)\longrightarrow \operatorname{cyclicPartner}\left(n, k, j\right) = \operatorname{slot}\left(n, 0\right)\\((k \operatorname{mod} 2 \ne 0)\land (j = 0))\longrightarrow \operatorname{cyclicPartner}\left(n, k, j\right) = \operatorname{slot}\left(n, k - 1\right)\\(((k \operatorname{mod} 2 \ne 0)\land (j \ne 0))\land (j + 1 = k))\longrightarrow \operatorname{cyclicPartner}\left(n, k, j\right) = \operatorname{slot}\left(n, 0\right)\\(((k \operatorname{mod} 2 \ne 0)\land (j \ne 0))\land (j + 1 \ne k))\longrightarrow \operatorname{cyclicPartner}\left(n, k, j\right) = \operatorname{slot}\left(n, j\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.cyclicPartner` (`✓ std3`).

*Citation.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Definition 3 uses the even or odd level rule. The physical top index k is one less than the level, and round index zero corresponds to the first swap.

**Definition 1.9 (The prescribed penultimate parking order).**

$$\forall(n:\mathbb{N}),[\operatorname{NeZero}\left(n\right)],\forall(j:\mathbb{N}),\begin{aligned}\operatorname{let} m:=\frac{n - 2}{2}\\(j < m)\longrightarrow \operatorname{penultimateItem}\left(n, j\right) = \operatorname{slot}\left(n, j\right)\\(m \le j)\longrightarrow \operatorname{penultimateItem}\left(n, j\right) = \operatorname{slot}\left(n, 3 \cdot m - 1 - j\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.penultimateItem` (`✓ std3`).

*Citation.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Definition 22 lists 1 through m first and then 2m through m+1 in decreasing order. The list items and round indices here are zero-based.

**Definition 1.10 (The ordered list of physical swaps).**

$$\forall(\alpha:Type),\forall(\mathit{lower}:\operatorname{List}\left(\alpha\times\alpha\right)),\forall(\mathit{top}:\alpha),\forall(s:\mathbb{N} \to \alpha),\forall(j:\mathbb{N}),\begin{aligned}\operatorname{orderedSweep}\left(\mathit{lower}, \mathit{top}, s, 0\right) = \mathit{lower}\\\operatorname{orderedSweep}\left(\mathit{lower}, \mathit{top}, s, j + 1\right) = \operatorname{orderedSweep}\left(\mathit{lower}, \mathit{top}, s, j\right)++(s\left(j\right),\mathit{top})::\mathit{lower}\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.orderedSweep` (`✓ std3`).

*Citation.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Section 3.1 calls the lower sweep first. Each round then performs its swap and starts the next lower call.

**Definition 1.11 (Executing the ordered swaps).**

$$\forall(\alpha:Type),[\operatorname{DecidableEq}\left(\alpha\right)],\forall(\mathit{swaps}:\operatorname{List}\left(\alpha\times\alpha\right)),\forall(\mathit{start}:\operatorname{Equiv.Perm}\left(\alpha\right)),\operatorname{executeSwaps}\left(\mathit{swaps}, \mathit{start}\right) = \operatorname{List.foldl}\left(\mathit{state}\mapsto \mathit{ab}\mapsto \operatorname{Equiv.swap}\left(\mathit{ab}.1, \mathit{ab}.2\right) \cdot \mathit{state}, \mathit{start}, \mathit{swaps}\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.executeSwaps` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

The state sends each item to its position, so a transposition of positions multiplies it on the left.

**Definition 1.12 (The recursive cyclic sweep).**

$$\forall(n:\mathbb{N}),[\operatorname{NeZero}\left(n\right)],\forall(k:\mathbb{N}),\begin{aligned}\operatorname{cyclicSweep}\left(n, 0\right) = []\\\operatorname{cyclicSweep}\left(n, k + 1\right) = \operatorname{orderedSweep}\left(\operatorname{cyclicSweep}\left(n, k\right), \operatorname{slot}\left(n, k + 1\right), \operatorname{cyclicPartner}\left(n, k + 1\right), k + 1\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.cyclicSweep` (`✓ std3`).

*Citation.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Level one has no physical swap. At higher levels the chosen partners are those of Definition 3.

**Theorem 1.13 (Net formula for a parking sweep).**

$$\forall(\alpha:Type),[\operatorname{DecidableEq}\left(\alpha\right)],\forall(\mathit{lower}:\operatorname{List}\left(\alpha\times\alpha\right)),\forall(\mathit{top}:\alpha),\forall(e:\mathbb{N} \to \alpha),\begin{aligned}\operatorname{let} C:=\operatorname{executeSwaps}\left(\mathit{lower}, 1\right)\\(C\left(\mathit{top}\right) = \mathit{top})\longrightarrow \forall(j:\mathbb{N}),\operatorname{executeSwaps}\left(\operatorname{orderedSweep}\left(\mathit{lower}, \mathit{top}, \operatorname{parkingPartner}\left(C, \mathit{top}, e\right), j\right), 1\right) = C^{j + 1} \cdot (\operatorname{path}\left(\mathit{top}, e, j\right)).formPerm\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.executeParkingSweep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Theorem 18(a)–(b) follows by conjugating the physical swap back to the prescribed items in each round, then collecting the transpositions in order.

**Definition 1.14 (The penultimate sweep of Definition 22).**

$$\forall(n:\mathbb{N}),[\operatorname{NeZero}\left(n\right)],\begin{aligned}\operatorname{let} \mathit{lower}:=\operatorname{cyclicSweep}\left(n, n - 3\right)\\\operatorname{let} \mathit{top}:=\operatorname{slot}\left(n, n - 2\right)\\\operatorname{penultimateSweep}\left(n\right) = \operatorname{orderedSweep}\left(\mathit{lower}, \mathit{top}, \operatorname{parkingPartner}\left(\operatorname{executeSwaps}\left(\mathit{lower}, 1\right), \mathit{top}, \operatorname{penultimateItem}\left(n\right)\right), n - 2\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.penultimateSweep` (`✓ std3`).

*Citation.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

The ambient carrier keeps the largest position available as a fixed point. The lower call is the cyclic sweep on the first n−2 positions.

**Definition 1.15 (The net of the penultimate sweep).**

$$\forall(n:\mathbb{N}),[\operatorname{NeZero}\left(n\right)],\operatorname{actualU}\left(n\right) = \operatorname{executeSwaps}\left(\operatorname{penultimateSweep}\left(n\right), 1\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.actualU` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

This net executes the penultimate sweep from the identity in the same carrier.

**Definition 1.16 (The quotient that prescribes the top order).**

$$\forall(n:\mathbb{N}),[\operatorname{NeZero}\left(n\right)],\operatorname{literalZ}\left(n\right) = \operatorname{actualU}\left(n\right)^{-(n:\mathbb{Z})} \cdot \operatorname{Fin.revPerm}$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.literalZ` (`✓ std3`).

*Citation.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Definition 22 places the target reversal on the right of the negative power of the actual penultimate net.

**Theorem 1.17 (Powers of the cycle of a list).**

$$\forall(\alpha:Type),[\operatorname{DecidableEq}\left(\alpha\right)],\forall(\mathit{label}:\mathbb{N} \to \alpha),\forall(L:\mathbb{N}),((\operatorname{List.ofFn}\left((i:\operatorname{Fin}\left(L\right))\mapsto \mathit{label}\left((i).val\right)\right)).Nodup)\longrightarrow \forall(p:\mathbb{N}),\forall(i:\mathbb{N}),(i < L)\longrightarrow \left((\operatorname{List.ofFn}\left((i:\operatorname{Fin}\left(L\right))\mapsto \mathit{label}\left((i).val\right)\right)).formPerm^{p}\right)\left(\mathit{label}\left(i\right)\right) = \mathit{label}\left((i + p) \operatorname{mod} L\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.formPerm_ofFn_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

A cycle advances by p indices modulo its length along the list of distinct labels.

**Theorem 1.18 (Distinct indices give distinct labels).**

$$\forall(\alpha:Type),\forall(\mathit{label}:\mathbb{N} \to \alpha),\forall(L:\mathbb{N}),(\forall(i:\mathbb{N}),(i < L)\longrightarrow \forall(j:\mathbb{N}),(j < L)\longrightarrow (\mathit{label}\left(i\right) = \mathit{label}\left(j\right))\longrightarrow i = j)\longrightarrow (\operatorname{List.ofFn}\left((i:\operatorname{Fin}\left(L\right))\mapsto \mathit{label}\left((i).val\right)\right)).Nodup$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.nodup_ofFn_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

The hypothesis compares labels only at in-range indices.

**Definition 1.19 (The coordinate formula for the penultimate net).**

$$\forall(m:\mathbb{N}),\forall(x:\mathbb{N}),\begin{aligned}(x = 2 \cdot m)\longrightarrow \operatorname{uArrow}\left(m, x\right) = 1\\((x \ne 2 \cdot m)\land (x + 1 < m))\longrightarrow \operatorname{uArrow}\left(m, x\right) = x + 2\\((x \ne 2 \cdot m)\land (x + 1 = m))\longrightarrow \operatorname{uArrow}\left(m, x\right) = 0\\(((x \ne 2 \cdot m)\land (m < x + 1))\land (x = m))\longrightarrow \operatorname{uArrow}\left(m, x\right) = 2 \cdot m\\(((x \ne 2 \cdot m)\land (m < x + 1))\land (x \ne m))\longrightarrow \operatorname{uArrow}\left(m, x\right) = x\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.uArrow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

The coordinate formula for the moving points uses m, half the size of the cyclic lower call.

**Theorem 1.20 (The actual net satisfies the coordinate formula).**

$$\forall(m:\mathbb{N}),(2 \le m)\longrightarrow \forall(x:\operatorname{Fin}\left(2 \cdot m + 2\right)),(\operatorname{actualU}\left(2 \cdot m + 2, x\right)).val = \operatorname{uArrow}\left(m, (x).val\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.literal_net_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

The cyclic lower net and the prescribed parking cycle compose to give the displayed value. The range includes every position of the ambient carrier.

**Definition 1.21 (The ordered sequence of visited states).**

$$\forall(\alpha:Type),[\operatorname{DecidableEq}\left(\alpha\right)],\forall(\mathit{swaps}:\operatorname{List}\left(\alpha\times\alpha\right)),\forall(\mathit{start}:\operatorname{Equiv.Perm}\left(\alpha\right)),\operatorname{sweepStates}\left(\mathit{swaps}, \mathit{start}\right) = \operatorname{List.scanl}\left(\mathit{state}\mapsto \mathit{ab}\mapsto \operatorname{Equiv.swap}\left(\mathit{ab}.1, \mathit{ab}.2\right) \cdot \mathit{state}, \mathit{start}, \mathit{swaps}\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.sweepStates` (`✓ std3`).

*Citation.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Section 3.1 emits an initial state and then one new state after each physical swap.

**Theorem 1.22 (Appending the next block of emissions).**

$$\forall(\alpha:Type),[\operatorname{DecidableEq}\left(\alpha\right)],\forall(\mathit{lower}:\operatorname{List}\left(\alpha\times\alpha\right)),\forall(\mathit{top}:\alpha),\forall(s:\mathbb{N} \to \alpha),\forall(j:\mathbb{N}),\forall(\mathit{start}:\operatorname{Equiv.Perm}\left(\alpha\right)),\begin{aligned}\operatorname{let} \mathit{previous}:=\operatorname{orderedSweep}\left(\mathit{lower}, \mathit{top}, s, j\right)\\\operatorname{sweepStates}\left(\operatorname{orderedSweep}\left(\mathit{lower}, \mathit{top}, s, j + 1\right), \mathit{start}\right) = \operatorname{sweepStates}\left(\mathit{previous}, \mathit{start}\right)++\operatorname{sweepStates}\left(\mathit{lower}, \operatorname{Equiv.swap}\left(s\left(j\right), \mathit{top}\right) \cdot \operatorname{executeSwaps}\left(\mathit{previous}, \mathit{start}\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.sweepStates_ordered_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

The next lower call begins with the state obtained by swapping the scheduled positions in the preceding terminal state.

**Definition 1.23 (Fixed positions outside a prefix).**

$$\forall(n:\mathbb{N}),\forall(k:\mathbb{N}),\forall(p:\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)),\operatorname{FixesOutside}\left(k, p\right) = (\forall(x:\operatorname{Fin}\left(n\right)),(k \le (x).val)\longrightarrow p\left(x\right) = x)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.FixesOutside` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

This predicate fixes the full complement of the initial prefix.

**Definition 1.24 (Complete enumeration of a prefix).**

$$\forall(n:\mathbb{N}),\forall(k:\mathbb{N}),\forall(\mathit{swaps}:\operatorname{List}\left(\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(n\right)\right)),\begin{aligned}\operatorname{let} \mathit{states}:=\operatorname{sweepStates}\left(\mathit{swaps}, 1\right)\\\operatorname{PrefixSweep}\left(k, \mathit{swaps}\right)\Leftrightarrow (((\mathit{states}).Nodup)\land ((\forall(p:\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)),p \in \mathit{states}\Leftrightarrow \operatorname{FixesOutside}\left(k, p\right))\land (\forall(\mathit{ab}:\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(n\right)),(\mathit{ab} \in \mathit{swaps})\longrightarrow ((\mathit{ab}.1).val < k)\land (((\mathit{ab}.2).val < k)\land (\mathit{ab}.1 \ne \mathit{ab}.2)))))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.PrefixSweep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

The unvisited positions are fixed in every emitted state. The actual swaps always exchange two distinct positions within the prefix.

**Theorem 1.25 (The net fixes unvisited positions).**

$$\forall(n:\mathbb{N}),\forall(k:\mathbb{N}),\forall(\mathit{lower}:\operatorname{List}\left(\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(n\right)\right)),(\operatorname{PrefixSweep}\left(k, \mathit{lower}\right))\longrightarrow \operatorname{FixesOutside}\left(k, \operatorname{executeSwaps}\left(\mathit{lower}, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.prefixNet_fixes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

The net is the last state in the visited list.

**Theorem 1.26 (Extending by the final position).**

$$\forall(n:\mathbb{N}),[\operatorname{NeZero}\left(n\right)],\forall(k:\mathbb{N}),\forall(\mathit{lower}:\operatorname{List}\left(\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(n\right)\right)),\forall(e:\mathbb{N} \to \operatorname{Fin}\left(n\right)),((k + 1 = n)\land ((\operatorname{PrefixSweep}\left(k, \mathit{lower}\right))\land (\forall(i:\mathbb{N}),(i \le k)\longrightarrow \forall(j:\mathbb{N}),(j \le k)\longrightarrow (\operatorname{parked}\left(\operatorname{slot}\left(n, k\right), e, i\right) = \operatorname{parked}\left(\operatorname{slot}\left(n, k\right), e, j\right))\longrightarrow i = j)))\longrightarrow \begin{aligned}\operatorname{let} s:=\operatorname{parkingPartner}\left(\operatorname{executeSwaps}\left(\mathit{lower}, 1\right), \operatorname{slot}\left(n, k\right), e\right)\\\operatorname{PrefixSweep}\left(k + 1, \operatorname{orderedSweep}\left(\mathit{lower}, \operatorname{slot}\left(n, k\right), s, k\right)\right)\\\forall(j:\mathbb{N}),(j < k)\longrightarrow (s\left(j\right)).val < k\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.extendParkingSweep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Distinct parked items yield disjoint fibers indexed by the preimage of the final position. The lower sweep enumerates each fiber in call order. This extension assumes the new position is the final one of the ambient carrier.

**Theorem 1.27 (Cyclic calls enumerate the moving prefix).**

$$\forall(n:\mathbb{N}),[\operatorname{NeZero}\left(n\right)],\forall(k:\mathbb{N}),(k < n)\longrightarrow \operatorname{PrefixSweep}\left(k + 1, \operatorname{cyclicSweep}\left(n, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.cyclic_prefixSweep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Induction on the level applies the parked-item decomposition and checks the distinct item order for both level parities.

**Theorem 1.28 (The prescribed penultimate call is complete).**

$$\forall(n:\mathbb{N}),[\operatorname{NeZero}\left(n\right)],((6 \le n)\land (n \operatorname{mod} 4 = 2))\longrightarrow \operatorname{PrefixSweep}\left(n - 1, \operatorname{penultimateSweep}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.penultimate_prefixSweep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

The two pieces of the prescribed parking order are disjoint and exhaust the moving items below the penultimate position.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.FixesOutside`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.PrefixSweep`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.actualU`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.cyclicPartner`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.cyclicSweep`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.cyclic_prefixSweep`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.executeParkingSweep`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.executeSwaps`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.extendParkingSweep`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.formPerm_ofFn_pow`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.initial`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.initial_nodup`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.literalZ`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.literal_net_value`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.nodup_ofFn_labels`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.orderedSweep`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.parked`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.parkingPartner`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.path`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.penultimateItem`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.penultimateSweep`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.penultimate_prefixSweep`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.prefixNet_fixes`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.slot`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.slot_val`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.sweepStates`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.sweepStates_ordered_succ`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep.uArrow`
