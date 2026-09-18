# Convergence of the Shieh-Yang-Yu Machine

## Abstract

Every permutation eventually reaches a fixed point of the 21̇-machine.

The source defines s_{21̇} through Baril's dotted patterns and PROVES the closed form of Proposition 3.5; this module takes that proved right-hand side (reverse each valley run) as the definition of `r`. The identification of the dotted-pattern stack with valley-run reversal is the source's own theorem and is NOT formalized here.

Words are lists of natural numbers. List, cons, nil, map, flatten, reverse, takeWhile, and dropWhile have their Lean list meanings. The Boolean predicate p(v,x) is decide(v ≤ x). Perm is List.Perm, and range'(1,n) is the list [1,...,n]. The notation Mᵗ(w) means Function.iterate M t w, so M⁰(w)=w. The cited paper supplies the definitions and the conjecture; the convergence proof below is new here. Conjecture 6.1 concerns a different machine.

**Definition 1.1 (Valleys).**

$$\forall earlier \in List\left(\mathbb{N}\right),\; \forall entry \in \mathbb{N},\; IsValley\left(earlier, entry\right) \Leftrightarrow (\forall a \in \mathbb{N},\; a \in earlier \Rightarrow entry < a)$$

*Formalization.* `D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.IsValley` (`✓ std3`).

*Citation.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

Section 2 (printed p. 3): “Similarly, a valley of π is an entry πᵢ of π such that πᵢ is less than each π₁, π₂, . . . , πᵢ₋₁.” The argument earlier is the prefix before entry; an empty prefix makes the first entry a valley.

**Definition 1.2 (The valley-run decomposition).**

$$\begin{aligned}valleyRuns\left(nil\left(\right)\right) = nil\left(\right)\\\forall v \in \mathbb{N},\; \forall tail \in List\left(\mathbb{N}\right),\; valleyRuns\left(cons\left(v, tail\right)\right) = cons\left(cons\left(v, takeWhile\left((x \mapsto decide\left((v \le x)\right)), tail\right)\right), valleyRuns\left(dropWhile\left((x \mapsto decide\left((v \le x)\right)), tail\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.valleyRuns` (`✓ std3`).

*Citation.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

Section 2 (printed p. 3): “Similarly, a valley run is defined as a maximal sequence of consecutive entries such that the first entry is a valley and no other entry is a valley.” The source example is 24315, whose valley runs are 243 and 15. Starting with v, takeWhile retains entries at least v, and dropWhile starts the next run at the first smaller entry. On permutations this gives the source's unique partition; the functions also accept arbitrary lists.

**Definition 1.3 (Reverse each valley run).**

$$\forall w \in List\left(\mathbb{N}\right),\; r\left(w\right) = flatten\left(map\left(reverse, valleyRuns\left(w\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.r` (`✓ std3`).

*Citation.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

Proposition 3.5 (printed p. 6): “Let π = V₁V₂ . . . Vₖ ∈ Sₙ. Then, s₂₁̇(π) = rev(V₁)rev(V₂) . . . rev(Vₖ).” Here valleyRuns(w) is the list [V₁,...,Vₖ], map reverses each member, and flatten concatenates the reversed runs in their original order. This displayed right-hand side defines r.

**Definition 1.4 (West's operational stack map).**

$$\exists westRun \in List\left(\mathbb{N}\right) \to \left(List\left(\mathbb{N}\right) \to List\left(\mathbb{N}\right)\right),\; \left(\left(\left((\forall w \in List\left(\mathbb{N}\right),\; s\left(w\right) = westRun\left(nil\left(\right), w\right)) \land (\forall stack \in List\left(\mathbb{N}\right),\; westRun\left(stack, nil\left(\right)\right) = stack)\right) \land (\forall x \in \mathbb{N},\; \forall xs \in List\left(\mathbb{N}\right),\; westRun\left(nil\left(\right), cons\left(x, xs\right)\right) = westRun\left(cons\left(x, nil\left(\right)\right), xs\right))\right) \land (\forall x \in \mathbb{N},\; \forall xs \in List\left(\mathbb{N}\right),\; \forall a \in \mathbb{N},\; \forall rest \in List\left(\mathbb{N}\right),\; a < x \Rightarrow westRun\left(cons\left(a, rest\right), cons\left(x, xs\right)\right) = cons\left(a, westRun\left(rest, cons\left(x, xs\right)\right)\right))\right) \land (\forall x \in \mathbb{N},\; \forall xs \in List\left(\mathbb{N}\right),\; \forall a \in \mathbb{N},\; \forall rest \in List\left(\mathbb{N}\right),\; x \le a \Rightarrow westRun\left(cons\left(a, rest\right), cons\left(x, xs\right)\right) = westRun\left(cons\left(x, cons\left(a, rest\right)\right), xs\right))$$

*Formalization.* `D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.s` (`✓ std3`).

*Citation.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

Section 1 (printed p. 1): “West’s stack-sorting map s processes the input permutation through a stack in a right greedy manner such that elements of the stack always increase from top to bottom (see for example, Figure 1).” The auxiliary westRun has stack head as top. It pops a top a when a < x, pushes x otherwise, and returns the remaining stack when input is empty. The equations below give this pop/push/flush algorithm, starting from nil.

**Definition 1.5 (The machine applies r before s).**

$$\forall w \in List\left(\mathbb{N}\right),\; M\left(w\right) = s\left(r\left(w\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.M` (`✓ std3`).

*Citation.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

Section 1 (printed p. 2): “Similarly, inspired by Cerbai, Claesson, and Ferrari’s [6] σ-machines, we establish τ̇-machines, which consist of the dotted pattern-avoiding map sτ̇ followed by s, and are to be denoted by s ◦ sτ̇.” The displayed composition specializes this order to the 21̇-machine, using Proposition 3.5 for its first map.

**Theorem 1.6 (Every permutation reaches a fixed point).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\forall w \in List\left(\mathbb{N}\right),\; Perm\left(w, range'\left(1, n\right)\right) \Rightarrow \left(\exists t \in \mathbb{N},\; \left(M^{t + 1}\right)\left(w\right) = \left(M^{t}\right)\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.result` (`✓ std3`). ∎

*Resolves.* `Problems/shieh-yang-yu-dotted-machine-fixed-point-convergence` (proved) by `D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"shieh-yang-yu-dotted-machine-fixed-point-convergence","declaration_gid":"D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.result","resolution_kind":"proved"} -->

*Citation.* Michael Yang, Hansen Shieh, Ashley Yu (2025). *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*. URL: <https://arxiv.org/abs/2411.11914v2>.

*Commentary.*

Conjecture 6.2 (printed p. 11): “All permutations in Sₙ for all n ≥ 1 are eventually mapped to a fixed point of the 21̇-machine after a finite number of iterations through the machine.” A permutation in Sₙ is encoded by Perm(w,range'(1,n)); n and t are natural numbers. Equality of successive iterates says precisely that Mᵗ(w) is fixed. Both component maps preserve the multiset of entries. Strong induction on word length proves that reverse(w) ≤ reverse(M(w)) in lexicographic order for every word without repetitions. Choose a reachable word with maximal reversed word in the finite set of permutations. The inequality is then an equality, and injectivity of reverse gives the fixed point.

## References

- Truth anchor: `D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.IsValley`
- Truth anchor: `D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.M`
- Truth anchor: `D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.r`
- Truth anchor: `D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.result`
- Truth anchor: `D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.s`
- Truth anchor: `D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.valleyRuns`
