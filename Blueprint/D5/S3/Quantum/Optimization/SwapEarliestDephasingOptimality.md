# Earliest-pair swapping minimizes dephasing

## Abstract

Every complete earliest-pair swapping history minimizes the accumulated dephasing for any finite list of natural ready times.

**Definition 1.1 (Merging adjacent segments).**

$$\forall \left(x: \operatorname{List}\left(\mathbb{N}\right)\right), \left(\forall \left(i: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.merge}\left(x, i\right): \operatorname{List}\left(\mathbb{N}\right)\right) = \operatorname{List.append}\left(\operatorname{List.take}\left(i, x\right), \operatorname{List.cons}\left(\operatorname{max}\left(\operatorname{List.getD}\left(x, i, 0\right), \operatorname{List.getD}\left(x, \left(i\right) + \left(1\right), 0\right)\right), \operatorname{List.drop}\left(\left(i\right) + \left(2\right), x\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.merge` (`✓ std3`).

*Citation.* Lars Kamin; Evgeny Shchukin; Frank Schmidt; Peter van Loock (2023). *Exact rate analysis for quantum repeaters with imperfect memories and entanglement swapping as soon as possible*. DOI: [10.1103/PhysRevResearch.5.023086](https://doi.org/10.1103/PhysRevResearch.5.023086). URL: <https://arxiv.org/abs/2203.10318v1>.

*Commentary.*

At a valid index i, replace the adjacent ready times by their maximum, retaining the prefix and suffix in their original order. This is the shortened list in the source's recurrences (skr.tex, lines 1039–1040 and 1060–1061). Indices start at zero. The function is defined at every natural index: an absent entry is read as zero, take retains the available prefix, and drop removes the indicated number of entries. List.getD(x,i,0) is optional indexing at i followed by Option.getD with default zero.

**Definition 1.2 (The dephasing of one swap).**

$$\forall \left(x: \operatorname{List}\left(\mathbb{N}\right)\right), \left(\forall \left(i: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.swapCost}\left(x, i\right): \mathbb{N}\right) = \operatorname{Nat.sub}\left(\operatorname{max}\left(\operatorname{List.getD}\left(x, i, 0\right), \operatorname{List.getD}\left(x, \left(i\right) + \left(1\right), 0\right)\right), \operatorname{min}\left(\operatorname{List.getD}\left(x, i, 0\right), \operatorname{List.getD}\left(x, \left(i\right) + \left(1\right), 0\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.swapCost` (`✓ std3`).

*Citation.* Lars Kamin; Evgeny Shchukin; Frank Schmidt; Peter van Loock (2023). *Exact rate analysis for quantum repeaters with imperfect memories and entanglement swapping as soon as possible*. DOI: [10.1103/PhysRevResearch.5.023086](https://doi.org/10.1103/PhysRevResearch.5.023086). URL: <https://arxiv.org/abs/2203.10318v1>.

*Commentary.*

The natural difference between the maximum and minimum of two ready times is their absolute difference. It is the dephasing contribution of one adjacent swap (skr.tex, lines 1049–1054). As in merge, an absent entry is read as zero. Nat.sub is subtraction truncated at zero.

**Definition 1.3 (An earliest adjacent pair).**

$$\forall \left(x: \operatorname{List}\left(\mathbb{N}\right)\right), \left(\forall \left(i: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.IsGreedyStep}\left(x, i\right)\right) \Leftrightarrow \left(\left(\left(i\right) + \left(1\right) < \operatorname{List.length}\left(x\right)\right) \land \left(\forall \left(j: \mathbb{N}\right), \left(\left(\left(j\right) + \left(1\right) < \operatorname{List.length}\left(x\right)\right) \Rightarrow \left(\operatorname{max}\left(\operatorname{List.getD}\left(x, i, 0\right), \operatorname{List.getD}\left(x, \left(i\right) + \left(1\right), 0\right)\right) \le \operatorname{max}\left(\operatorname{List.getD}\left(x, j, 0\right), \operatorname{List.getD}\left(x, \left(j\right) + \left(1\right), 0\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.IsGreedyStep` (`✓ std3`).

*Citation.* Lars Kamin; Evgeny Shchukin; Frank Schmidt; Peter van Loock (2023). *Exact rate analysis for quantum repeaters with imperfect memories and entanglement swapping as soon as possible*. DOI: [10.1103/PhysRevResearch.5.023086](https://doi.org/10.1103/PhysRevResearch.5.023086). URL: <https://arxiv.org/abs/2203.10318v1>.

*Commentary.*

A greedy step has a valid adjacent-pair index, and the maximum of its two ready times is no greater than that of any other valid adjacent pair. This is the earliest-pair rule (skr.tex, lines 1033–1044). Equality permits every tie choice.

**Definition 1.4 (One minimization step).**

$$\forall \left(v: \left(\operatorname{List}\left(\mathbb{N}\right)\right) \to \left(\mathbb{N}\right)\right), \left(\forall \left(x: \operatorname{List}\left(\mathbb{N}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.bellman}\left(v, x\right): \mathbb{N}\right) = \operatorname{ite}\left(1 < \operatorname{List.length}\left(x\right), \min_{\left(i: \mathbb{N}\right), i < \operatorname{Nat.sub}\left(\operatorname{List.length}\left(x\right), 1\right)} \left(\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.swapCost}\left(x, i\right)\right) + \left(v\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.merge}\left(x, i\right)\right)\right)\right), 0\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.bellman` (`✓ std3`).

*Citation.* Lars Kamin; Evgeny Shchukin; Frank Schmidt; Peter van Loock (2023). *Exact rate analysis for quantum repeaters with imperfect memories and entanglement swapping as soon as possible*. DOI: [10.1103/PhysRevResearch.5.023086](https://doi.org/10.1103/PhysRevResearch.5.023086). URL: <https://arxiv.org/abs/2203.10318v1>.

*Commentary.*

Given a natural-valued continuation v, minimize the swap cost plus v of the merged list over all valid first swaps. The finite minimum is taken over i in Finset.range(length(x) − 1); that set is nonempty in the first branch. Lists of length zero or one have value zero. This extends the source's recurrence (skr.tex, lines 1053–1064) to terminal lists.

**Definition 1.5 (The optimal dephasing).**

$$\forall \left(x: \operatorname{List}\left(\mathbb{N}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.dstar}\left(x\right): \mathbb{N}\right) = \operatorname{Function.iterate}\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.bellman}, \operatorname{List.length}\left(x\right)\right)\left(\operatorname{Function.const}\left(\operatorname{List}\left(\mathbb{N}\right), \left(0: \mathbb{N}\right)\right), x\right)\right)$$

*Formalization.* `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.dstar` (`✓ std3`).

*Citation.* Lars Kamin; Evgeny Shchukin; Frank Schmidt; Peter van Loock (2023). *Exact rate analysis for quantum repeaters with imperfect memories and entanglement swapping as soon as possible*. DOI: [10.1103/PhysRevResearch.5.023086](https://doi.org/10.1103/PhysRevResearch.5.023086). URL: <https://arxiv.org/abs/2203.10318v1>.

*Commentary.*

Apply the Bellman operator length(x) times to the constant zero function and evaluate at x. Each valid merge removes one entry, so this many steps includes every complete sequence of swaps. This expresses the source's optimal dephasing recurrence and its two-segment base case (skr.tex, lines 1058–1064), with value zero on empty and singleton lists. Function.iterate counts applications of an operator; Function.const displays the constant zero function.

**Definition 1.6 (A complete earliest-pair history).**

$$\forall \left(x: \operatorname{List}\left(\mathbb{N}\right)\right), \left(\forall \left(hs: \operatorname{List}\left(\mathbb{N}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.IsGreedyRun}\left(x, hs\right)\right) \Leftrightarrow \left(\operatorname{List.foldr}\left(\lambda \left(i: \mathbb{N}\right) \mapsto \left(\lambda \left(r: \left(\operatorname{List}\left(\mathbb{N}\right)\right) \to \left(\operatorname{Prop}\right)\right) \mapsto \left(\lambda \left(y: \operatorname{List}\left(\mathbb{N}\right)\right) \mapsto \left(\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.IsGreedyStep}\left(y, i\right)\right) \land \left(r\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.merge}\left(y, i\right)\right)\right)\right)\right)\right), \lambda \left(y: \operatorname{List}\left(\mathbb{N}\right)\right) \mapsto \left(\operatorname{List.length}\left(y\right) \le 1\right), hs, x\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.IsGreedyRun` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lars Kamin; Evgeny Shchukin; Frank Schmidt; Peter van Loock (2023). *Exact rate analysis for quantum repeaters with imperfect memories and entanglement swapping as soon as possible*. DOI: [10.1103/PhysRevResearch.5.023086](https://doi.org/10.1103/PhysRevResearch.5.023086). URL: <https://arxiv.org/abs/2203.10318v1>.

*Commentary.*

The list hs records successive adjacent-pair indices in the changing list. The right fold constructs a predicate on the initial list: each recorded index must be greedy at that stage, and the final list must have length at most one. Thus the history expresses repeated earliest-pair choices from skr.tex, lines 1033–1040, while retaining every tie choice explicitly.

**Definition 1.7 (Accumulated dephasing along a history).**

$$\forall \left(x: \operatorname{List}\left(\mathbb{N}\right)\right), \left(\forall \left(hs: \operatorname{List}\left(\mathbb{N}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.runCost}\left(x, hs\right): \mathbb{N}\right) = \operatorname{List.foldr}\left(\lambda \left(i: \mathbb{N}\right) \mapsto \left(\lambda \left(r: \left(\operatorname{List}\left(\mathbb{N}\right)\right) \to \left(\mathbb{N}\right)\right) \mapsto \left(\lambda \left(y: \operatorname{List}\left(\mathbb{N}\right)\right) \mapsto \left(\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.swapCost}\left(y, i\right)\right) + \left(r\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.merge}\left(y, i\right)\right)\right)\right)\right)\right), \operatorname{Function.const}\left(\operatorname{List}\left(\mathbb{N}\right), \left(0: \mathbb{N}\right)\right), hs, x\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.runCost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lars Kamin; Evgeny Shchukin; Frank Schmidt; Peter van Loock (2023). *Exact rate analysis for quantum repeaters with imperfect memories and entanglement swapping as soon as possible*. DOI: [10.1103/PhysRevResearch.5.023086](https://doi.org/10.1103/PhysRevResearch.5.023086). URL: <https://arxiv.org/abs/2203.10318v1>.

*Commentary.*

The right fold constructs a function of the current list, adding the present swap cost to the remaining cost on the merged list. The empty history contributes zero. This function is defined for every hs; the greedy-run predicate separately requires valid indices and completion. On such histories it sums the contributions in skr.tex, lines 1039–1040. Function.const gives the terminal zero function.

**Definition 1.8 (Optimality for every complete greedy history).**

$$\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.claim}\right) \Leftrightarrow \left(\forall \left(x: \operatorname{List}\left(\mathbb{N}\right)\right), \left(\forall \left(hs: \operatorname{List}\left(\mathbb{N}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.IsGreedyRun}\left(x, hs\right)\right) \Rightarrow \left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.runCost}\left(x, hs\right) = \operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.dstar}\left(x\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lars Kamin; Evgeny Shchukin; Frank Schmidt; Peter van Loock (2023). *Exact rate analysis for quantum repeaters with imperfect memories and entanglement swapping as soon as possible*. DOI: [10.1103/PhysRevResearch.5.023086](https://doi.org/10.1103/PhysRevResearch.5.023086). URL: <https://arxiv.org/abs/2203.10318v1>.

*Commentary.*

For every finite list x of natural ready times and every complete greedy history hs, the accumulated dephasing equals dstar(x). This includes the conjecture in skr.tex, lines 1080–1084, for every length at least two and positive ready times. It also includes zero ready times and the empty and singleton lists; no particular tie choice is required.

**Theorem 1.9 (Every earliest-pair history attains the minimum).**

$$\forall \left(x: \operatorname{List}\left(\mathbb{N}\right)\right), \left(\forall \left(hs: \operatorname{List}\left(\mathbb{N}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.IsGreedyRun}\left(x, hs\right)\right) \Rightarrow \left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.runCost}\left(x, hs\right) = \operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.dstar}\left(x\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.result` (`✓ std3`). ∎

*Resolves.* `Problems/kamin-shchukin-schmidt-van-loock-2023-swap-earliest-dephasing` (proved) by `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kamin-shchukin-schmidt-van-loock-2023-swap-earliest-dephasing","declaration_gid":"D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Lars Kamin; Evgeny Shchukin; Frank Schmidt; Peter van Loock (2023). *Exact rate analysis for quantum repeaters with imperfect memories and entanglement swapping as soon as possible*. DOI: [10.1103/PhysRevResearch.5.023086](https://doi.org/10.1103/PhysRevResearch.5.023086). URL: <https://arxiv.org/abs/2203.10318v1>.

*Commentary.*

The three anonymous expressions below give the list maximum (zero on the empty list), the integer-valued potential, and the integer-valued boundary function, respectively. In the prose, denote their values by M(x), φ(x), and B(p,x). Every Int.ofNat explicitly includes a natural number in the integers.

$$
\begin{aligned}\lambda \left(x: \operatorname{List}\left(\mathbb{N}\right)\right) \mapsto \left(\operatorname{List.foldr}\left(\operatorname{max}, 0, x\right)\right)\\\lambda \left(x: \operatorname{List}\left(\mathbb{N}\right)\right) \mapsto \left(\left(\left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.foldr}\left(\operatorname{max}, 0, x\right)\right): \mathbb{Z}\right)\right) + \left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.sum}\left(\operatorname{List.zipWith}\left(\operatorname{max}, x, \operatorname{List.tail}\left(x\right)\right)\right)\right): \mathbb{Z}\right)\right)\right) - \left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.sum}\left(x\right)\right): \mathbb{Z}\right)\right)\right)\\\lambda \left(p: \mathbb{N}\right) \mapsto \left(\lambda \left(x: \operatorname{List}\left(\mathbb{N}\right)\right) \mapsto \left(\left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.sum}\left(\operatorname{List.zipWith}\left(\operatorname{max}, \operatorname{List.cons}\left(p, x\right), x\right)\right)\right): \mathbb{Z}\right)\right) - \left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.sum}\left(x\right)\right): \mathbb{Z}\right)\right)\right)\right)\end{aligned}
$$

The auxiliary function B separates the first entry: B(p,a :: x) is Int.ofNat(max(p,a)) − Int.ofNat(a) + B(a,x). A merge beyond the first entry commutes with retaining that entry. Every valid merge shortens the list by one and leaves M unchanged. Expanding the sums also gives φ(x) = B(M(x),x), including the empty list.

Next induct on the merge index to compare B before and after any valid merge. For a first pair a,b with a ≤ b, the swap cost plus the new B minus the old B is Int.ofNat(max(p,b)) − Int.ofNat(max(p,a)). For a ≥ b it is Int.ofNat(max(a,c)) − Int.ofNat(max(b,c)) if a following entry c exists, and zero if none exists. Both differences are nonnegative. For a later pair the first-entry expansion reduces the comparison to the shorter suffix.

The same induction gives equality when the chosen pair has least maximum among all adjacent pairs of p :: x. If a < b, comparison with the pair p,a forces p ≥ b, making the first difference zero. If a > b and c exists, comparison with b,c forces c ≥ a, making the second difference zero. Equal ready times and an absent following entry give zero directly. In the induction step, comparisons in the suffix are inherited by shifting the competing index by one.

Now take p = M(x). The additional leading pair M(x),x₀ has maximum M(x), which bounds the maximum of every valid chosen pair. Consequently a greedy pair in x remains least after this entry is prepended. The identity φ(x) = B(M(x),x) and preservation of M therefore give the two comparisons below.

$$
\begin{aligned}\forall \left(x: \operatorname{List}\left(\mathbb{N}\right)\right), \left(\forall \left(i: \mathbb{N}\right), \left(\left(\left(i\right) + \left(1\right) < \operatorname{List.length}\left(x\right)\right) \Rightarrow \left(\left(\left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.foldr}\left(\operatorname{max}, 0, x\right)\right): \mathbb{Z}\right)\right) + \left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.sum}\left(\operatorname{List.zipWith}\left(\operatorname{max}, x, \operatorname{List.tail}\left(x\right)\right)\right)\right): \mathbb{Z}\right)\right)\right) - \left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.sum}\left(x\right)\right): \mathbb{Z}\right)\right) \le \left(\left(\operatorname{Int.ofNat}\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.swapCost}\left(x, i\right)\right): \mathbb{Z}\right)\right) + \left(\left(\left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.foldr}\left(\operatorname{max}, 0, \operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.merge}\left(x, i\right)\right)\right): \mathbb{Z}\right)\right) + \left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.sum}\left(\operatorname{List.zipWith}\left(\operatorname{max}, \operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.merge}\left(x, i\right), \operatorname{List.tail}\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.merge}\left(x, i\right)\right)\right)\right)\right): \mathbb{Z}\right)\right)\right) - \left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.sum}\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.merge}\left(x, i\right)\right)\right): \mathbb{Z}\right)\right)\right)\right)\right)\right)\\\forall \left(x: \operatorname{List}\left(\mathbb{N}\right)\right), \left(\forall \left(i: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.IsGreedyStep}\left(x, i\right)\right) \Rightarrow \left(\left(\left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.foldr}\left(\operatorname{max}, 0, x\right)\right): \mathbb{Z}\right)\right) + \left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.sum}\left(\operatorname{List.zipWith}\left(\operatorname{max}, x, \operatorname{List.tail}\left(x\right)\right)\right)\right): \mathbb{Z}\right)\right)\right) - \left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.sum}\left(x\right)\right): \mathbb{Z}\right)\right) = \left(\left(\operatorname{Int.ofNat}\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.swapCost}\left(x, i\right)\right): \mathbb{Z}\right)\right) + \left(\left(\left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.foldr}\left(\operatorname{max}, 0, \operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.merge}\left(x, i\right)\right)\right): \mathbb{Z}\right)\right) + \left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.sum}\left(\operatorname{List.zipWith}\left(\operatorname{max}, \operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.merge}\left(x, i\right), \operatorname{List.tail}\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.merge}\left(x, i\right)\right)\right)\right)\right): \mathbb{Z}\right)\right)\right) - \left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.sum}\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.merge}\left(x, i\right)\right)\right): \mathbb{Z}\right)\right)\right)\right)\right)\right)\end{aligned}
$$

Whenever the list has more than one entry, the nonempty finite set of adjacent-pair indices has an index minimizing its pair maximum, hence a greedy step exists. On lists of length at most one, direct evaluation gives φ(x) = 0.

Induct on n to identify n Bellman iterations with φ for every x of length at most n. At n = 0 the list is empty. At a successor, terminal lists again give zero. For a nonterminal list, each merged list is short enough for the induction hypothesis. Choosing a greedy first pair bounds the Bellman minimum above by φ(x), using the equality comparison. Choosing an index attaining that minimum bounds it below by φ(x), using the comparison for every valid pair. The two bounds agree. Setting n = length(x) identifies Int.ofNat(dstar(x)) with φ(x).

$$
\forall \left(n: \mathbb{N}\right), \left(\forall \left(x: \operatorname{List}\left(\mathbb{N}\right)\right), \left(\left(\operatorname{List.length}\left(x\right) \le n\right) \Rightarrow \left(\left(\operatorname{Int.ofNat}\left(\operatorname{Function.iterate}\left(\operatorname{D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality.bellman}, n\right)\left(\operatorname{Function.const}\left(\operatorname{List}\left(\mathbb{N}\right), \left(0: \mathbb{N}\right)\right), x\right)\right): \mathbb{Z}\right) = \left(\left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.foldr}\left(\operatorname{max}, 0, x\right)\right): \mathbb{Z}\right)\right) + \left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.sum}\left(\operatorname{List.zipWith}\left(\operatorname{max}, x, \operatorname{List.tail}\left(x\right)\right)\right)\right): \mathbb{Z}\right)\right)\right) - \left(\left(\operatorname{Int.ofNat}\left(\operatorname{List.sum}\left(x\right)\right): \mathbb{Z}\right)\right)\right)\right)\right)
$$

Finally induct on hs. For the empty greedy history the list is terminal, so its cost and φ are zero. For i :: hs, the greedy-run predicate supplies a greedy first step and a complete greedy remaining history on merge(x,i). Cast the cost sum into the integers, apply the induction hypothesis to that remaining history, and use the greedy-step equality to obtain Int.ofNat(runCost(x,i :: hs)) = φ(x). Combining this identity with Int.ofNat(dstar(x)) = φ(x) and injectivity of Int.ofNat proves the stated natural-number equality. The argument includes all natural ready times and every permitted tie choice.

## References

- Truth anchor: `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.IsGreedyRun`
- Truth anchor: `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.IsGreedyStep`
- Truth anchor: `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.bellman`
- Truth anchor: `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.claim`
- Truth anchor: `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.dstar`
- Truth anchor: `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.merge`
- Truth anchor: `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.result`
- Truth anchor: `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.runCost`
- Truth anchor: `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.swapCost`
