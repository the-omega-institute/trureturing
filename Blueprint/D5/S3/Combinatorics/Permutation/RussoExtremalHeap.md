# Russo’s extremal Heap sweep

## Abstract

The extremal Heap sweep ends in reversal for sizes two modulo four.

A state sends each item to its position. An array sends each position to its item, so the emitted arrays are the inverses of the states. Position zero is position one of the paper. Products act from right to left.

**Definition 1.1 (Items prescribed at the highest level).**

$$\forall(n:\mathbb{N}),[\operatorname{NeZero}\left(n\right)],\forall(j:\mathbb{N}),\operatorname{topParkingItem}\left(n, j\right) = \left(\operatorname{literalZ}\left(n\right)^{j + 1}\right)\left(\operatorname{slot}\left(n, n - 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoExtremalHeap.topParkingItem` (`✓ std3`).

*Citation.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Definition 22 reads the successive positive powers of the quotient at the last position. The zero power gives the item already parked there.

**Definition 1.2 (The physical top-level partner).**

$$\forall(n:\mathbb{N}),[\operatorname{NeZero}\left(n\right)],\forall(j:\mathbb{N}),\operatorname{extremalTopPartner}\left(n, j\right) = \operatorname{parkingPartner}\left(\operatorname{actualU}\left(n\right), \operatorname{slot}\left(n, n - 1\right), \operatorname{topParkingItem}\left(n\right), j\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoExtremalHeap.extremalTopPartner` (`✓ std3`).

*Citation.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Theorem 18(a) recovers the physical partner from the prescribed item by advancing the current state through the lower call.

**Definition 1.3 (The ordered physical sweep).**

$$\forall(n:\mathbb{N}),[\operatorname{NeZero}\left(n\right)],(n = 2\longrightarrow\operatorname{extremalSweep}\left(n\right) = \operatorname{cyclicSweep}\left(n, 1\right))\land (n \ne 2\longrightarrow \operatorname{extremalSweep}\left(n\right) = \operatorname{orderedSweep}\left(\operatorname{penultimateSweep}\left(n\right), \operatorname{slot}\left(n, n - 1\right), \operatorname{extremalTopPartner}\left(n\right), n - 1\right))$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoExtremalHeap.extremalSweep` (`✓ std3`).

*Citation.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Definition 22 uses the cyclic or classic call at size two. At larger admissible sizes the penultimate calls occur in the order fixed by the computed top partners.

**Definition 1.4 (The ordered emitted arrays).**

$$\forall(\alpha:Type),[\operatorname{DecidableEq}\left(\alpha\right)],\forall(\mathit{swaps}:\operatorname{List}\left(\alpha\times\alpha\right)),\forall(\mathit{start}:\operatorname{Equiv.Perm}\left(\alpha\right)),\operatorname{sweepArrays}\left(\mathit{swaps}, \mathit{start}\right) = (\operatorname{sweepStates}\left(\mathit{swaps}, \mathit{start}\right)).map\left(\mathit{state}\mapsto (\mathit{state})^{-1}\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/RussoExtremalHeap.sweepArrays` (`✓ std3`).

*Citation.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Section 3.1 emits the starting state followed by the state immediately after each physical swap. Inversion reads each state as an array.

**Theorem 1.5 (Exact enumeration and reversal in the residue-two class).**

$$\begin{aligned}\operatorname{extremalSweep}\left(2\right) = [(0,1)]\\\operatorname{sweepArrays}\left(\operatorname{extremalSweep}\left(2\right), 1\right) = [1,\operatorname{Fin.revPerm}]\\\forall(n:\mathbb{N}),((2 \le n)\land (n \operatorname{mod} 4 = 2))\longrightarrow \begin{aligned}\operatorname{let} \mathit{swaps}:=\operatorname{extremalSweep}\left(n\right)\\\operatorname{let} \mathit{emitted}:=\operatorname{sweepArrays}\left(\mathit{swaps}, 1\right)\\\mathit{emitted}[0] = \operatorname{some}\left(1\right)\\(\mathit{emitted}).Nodup\\\forall(\mathit{array}:\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)),\mathit{array} \in \mathit{emitted}\\(\mathit{emitted}).length = (n).factorial\\(\mathit{emitted}).IsChain\left(p\mapsto q\mapsto \exists(a:\operatorname{Fin}\left(n\right)),\exists(b:\operatorname{Fin}\left(n\right)),(a \ne b)\land (q = p \cdot \operatorname{Equiv.swap}\left(a, b\right))\right)\\\forall(i:\mathbb{N}),\mathit{emitted}[i + 1] = (\mathit{emitted}[i]).bind\left(\mathit{array}\mapsto (\mathit{swaps}[i]).map\left(\mathit{ab}\mapsto \mathit{array} \cdot \operatorname{Equiv.swap}\left(\mathit{ab}.1, \mathit{ab}.2\right)\right)\right)\\\mathit{emitted}[(\mathit{emitted}).length - 1] = \operatorname{some}\left(\operatorname{Fin.revPerm}\right)\\(\operatorname{executeSwaps}\left(\mathit{swaps}, 1\right))^{-1} = \operatorname{Fin.revPerm}\\\forall(\mathit{array}:\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)),\mathit{array} = \operatorname{Fin.revPerm}\lor\operatorname{Pi.Lex}\left((<), (<), i\mapsto \mathit{array}\left(i\right), i\mapsto \operatorname{Fin.rev}\left(i\right)\right)\\\forall(\mathit{ab}:\operatorname{Fin}\left(n\right)\times\operatorname{Fin}\left(n\right)),(\mathit{ab} \in \mathit{swaps})\longrightarrow \mathit{ab}.1 \ne \mathit{ab}.2\\(6 \le n)\longrightarrow \begin{aligned}(\operatorname{literalZ}\left(n\right)).IsCycleOn\left(\operatorname{Set.univ}\left(\right)\right)\\\operatorname{Function.Bijective}\left((j:\operatorname{Fin}\left(n\right))\mapsto \left(\operatorname{literalZ}\left(n\right)^{(j).val}\right)\left(\operatorname{slot}\left(n, n - 1\right)\right)\right)\\\forall(j:\mathbb{N}),(j < n - 1)\longrightarrow (\operatorname{extremalTopPartner}\left(n, j\right)).val < n - 1\\\operatorname{executeSwaps}\left(\mathit{swaps}, 1\right) = \operatorname{actualU}\left(n\right)^{n} \cdot \operatorname{literalZ}\left(n\right)\\\operatorname{actualU}\left(n\right)^{n} \cdot \operatorname{literalZ}\left(n\right) = \operatorname{Fin.revPerm}\\\forall(i:\mathbb{N}),(i < n - 1)\longrightarrow \begin{aligned}\operatorname{let} \mathit{lower}:=\operatorname{penultimateSweep}\left(n\right)\\\operatorname{let} \mathit{previous}:=\operatorname{orderedSweep}\left(\mathit{lower}, \operatorname{slot}\left(n, n - 1\right), \operatorname{extremalTopPartner}\left(n\right), i\right)\\\operatorname{let} \mathit{last}:=\operatorname{executeSwaps}\left(\mathit{previous}, 1\right)\\\operatorname{let} \tau:=\operatorname{Equiv.swap}\left(\operatorname{extremalTopPartner}\left(n, i\right), \operatorname{slot}\left(n, n - 1\right)\right)\\\operatorname{sweepArrays}\left(\operatorname{orderedSweep}\left(\mathit{lower}, \operatorname{slot}\left(n, n - 1\right), \operatorname{extremalTopPartner}\left(n\right), i + 1\right), 1\right) = \operatorname{sweepArrays}\left(\mathit{previous}, 1\right)++\operatorname{sweepArrays}\left(\mathit{lower}, \tau \cdot \mathit{last}\right)\\\operatorname{sweepArrays}\left(\mathit{previous}, 1\right)[(\operatorname{sweepArrays}\left(\mathit{previous}, 1\right)).length - 1] = \operatorname{some}\left((\mathit{last})^{-1}\right)\\\operatorname{sweepArrays}\left(\mathit{lower}, \tau \cdot \mathit{last}\right)[0] = \operatorname{some}\left((\mathit{last})^{-1} \cdot \tau\right)\end{aligned}\end{aligned}\end{aligned}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/RussoExtremalHeap.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luís M. S. Russo (2026). *Heap-type permutation generation with a prescribed final arrangement*. DOI: [10.48550/arXiv.2611.22780](https://doi.org/10.48550/arXiv.2611.22780). URL: <https://arxiv.org/abs/2611.22780v1>.

*Commentary.*

Section 10 item 1 asks for the case n congruent to two modulo four. At n = 2 the cyclic call swaps zero and one. For n at least six the quotient is formed using the actual net of the penultimate sweep. Its entire orbit gives the prescribed order, and every recorded partner lies below the last position.

The first return to the support of the penultimate net is the square of its even cycle after a transposition of consecutive support coordinates. This joins the two alternating cycles. An excursion has length one or two, and every point outside the support is the intermediate point of a two-step return. The full-carrier orbit follows from the project’s first-visit theorem.

The parked item distinguishes the recursive blocks. Each block runs through its own fiber in lower-call order. The stored swap connects the last array of the preceding block and the first array of the next block. The net is the lower net to the nth power followed, in composition order, by the quotient. Reversal is maximal because, at the first unequal position, the larger candidate entries already occur in the shared prefix.

Brackets on a list in an optional lookup return some entry when the index is in range and none otherwise. Index zero and the index one less than the length give the displayed head and last queries on these nonempty lists. The step formula includes the optional lookup on the swap list at every natural index.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoExtremalHeap.extremalSweep`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoExtremalHeap.extremalTopPartner`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoExtremalHeap.result`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoExtremalHeap.sweepArrays`
- Truth anchor: `D5/S3/Combinatorics/Permutation/RussoExtremalHeap.topParkingItem`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing](../PerfectMatchings/FiniteEndpointPairing.md)
- Dependency: [D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep](RussoHeapLowerSweep.md)
