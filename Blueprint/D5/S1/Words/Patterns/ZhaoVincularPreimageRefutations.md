# Two Vincular-Stack Preimage Conjectures Are False

## Abstract

Zhao's maximum and second-largest vincular-stack fibre conjectures are false.

The right-greedy convention reads input from left to right. It pushes the next letter if the entire proposed stack avoids the pattern, and otherwise pops the top letter to the output and retries. After the input ends it drains the stack. This is the Cerbai–Claesson–Ferrari convention: the source describes right-greedy processing without a formal stack-rule definition. Its four worked figures send 514362 to 463215, 263415, 426315, and 632415 for the four displayed patterns; the fourth uses 1-underline(23).

**Definition 1.1 (Whole-stack vincular containment).**

$$\forall d \in Bool, w \in List\left(\mathrm{Nat}\right),\; Contains\left(d, w\right) \Leftrightarrow (\exists i \in Fin\left(length\left(w\right)\right), j \in Fin\left(length\left(w\right)\right),\; val\left(i\right) < val\left(j\right) \land \left(val\left(j\right) + 1 < length\left(w\right) \land if\left(d, (getElem!\left(w, val\left(i\right)\right) > getElem!\left(w, val\left(j\right)\right) \land getElem!\left(w, val\left(j\right)\right) > getElem!\left(w, val\left(j\right) + 1\right)), (getElem!\left(w, val\left(i\right)\right) < getElem!\left(w, val\left(j\right)\right) \land getElem!\left(w, val\left(j\right)\right) < getElem!\left(w, val\left(j\right) + 1\right))\right)\right))$$

*Formalization.* `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.Contains` (`✓ std3`).

*Citation.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

On page 1, Zhao writes: “When considering whether a permutation π contains a vincular pattern σ, some elements may be required to be adjacent in π, as indicated by underlined terms in σ. For instance, the pattern 1423 contains 12̲3̲ and 123, but avoids 1̲2̲3 and 1̲2̲3̲.” The letters are natural numbers with one-based permutation entries. Stack words are read from top to bottom. The Bool flag false denotes 1-underline(23), and true denotes 3-underline(21). Underlined entries must occupy adjacent positions. The indices i and j in Contains are zero-based Fin values; getElem! is list indexing with default zero, and the bounds ensure that every index used here is valid. Subtraction is natural subtraction, truncated at zero; the conjectures' lower bounds make their exponents ordinary nonnegative differences.

**Definition 1.2 (Decidable containment).**

$$\forall d \in Bool, w \in List\left(\mathrm{Nat}\right),\; decidableContains\left(d, w\right): Decidable\left(Contains\left(d, w\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.decidableContains` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Unfolding Contains leaves two quantifiers over finite position types and decidable natural-number comparisons; inferInstance supplies the decision procedure.

**Definition 1.3 (Push or pop and retry).**

$$\begin{aligned}\forall d \in Bool, x \in \mathrm{Nat},\; Push\left(d, x, nil\right) = (nil, cons\left(x, nil\right))\\\forall d \in Bool, x \in \mathrm{Nat}, a \in \mathrm{Nat}, s \in List\left(\mathrm{Nat}\right),\; Push\left(d, x, cons\left(a, s\right)\right) = if\left(Contains\left(d, cons\left(x, cons\left(a, s\right)\right)\right), (\operatorname{let} r := Push\left(d, x, s\right), (cons\left(a, fst\left(r\right)\right), snd\left(r\right))), (nil, cons\left(x, cons\left(a, s\right)\right))\right)\end{aligned}$$

*Formalization.* `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.Push` (`✓ std3`).

*Citation.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

The result is the pair of emitted letters and remaining stack. In the recursive case r is Push(d,x,s). The test examines the whole proposed stack cons(x,cons(a,s)).

**Definition 1.4 (Process and drain).**

$$\begin{aligned}\forall d \in Bool, s \in List\left(\mathrm{Nat}\right),\; Process\left(d, nil, s\right) = s\\\forall d \in Bool, x \in \mathrm{Nat}, xs \in List\left(\mathrm{Nat}\right), s \in List\left(\mathrm{Nat}\right),\; Process\left(d, cons\left(x, xs\right), s\right) = \operatorname{let} r := Push\left(d, x, s\right), append\left(fst\left(r\right), Process\left(d, xs, snd\left(r\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.Process` (`✓ std3`).

*Citation.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

The first list is unprocessed input and the second is the stack. Append is list concatenation, and fst and snd are the two projections of a pair.

**Definition 1.5 (The right-greedy map).**

$$\forall d \in Bool, input \in List\left(\mathrm{Nat}\right),\; SC\left(d, input\right) = Process\left(d, input, nil\right)$$

*Formalization.* `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.SC` (`✓ std3`).

*Citation.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Processing starts with the empty stack nil. The map is defined on all natural-number words, and its fibres below restrict the inputs to permutations.

**Definition 1.6 (Permutations on one-based entries).**

$$\forall n \in \mathrm{Nat}, p \in List\left(\mathrm{Nat}\right),\; IsPerm\left(n, p\right) \Leftrightarrow Perm\left(p, range'\left(1, n\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.IsPerm` (`✓ std3`).

*Citation.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Perm is List.Perm. The list List.range' 1 n is the entries 1 through n in increasing order.

**Definition 1.7 (Decidable permutation membership).**

$$\forall n \in \mathrm{Nat}, p \in List\left(\mathrm{Nat}\right),\; decidableIsPerm\left(n, p\right): Decidable\left(IsPerm\left(n, p\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.decidableIsPerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Unfolding IsPerm gives decidable list permutation on natural-number entries; inferInstance supplies the decision procedure.

**Definition 1.8 (Enumeration of all permutations).**

$$\forall n \in \mathrm{Nat},\; Sn\left(n\right) = permutations'\left(range'\left(1, n\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.Sn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

List.permutations' is the structural permutation enumerator. Its membership is List.Perm with the original list. Because List.range' 1 n has distinct entries, this enumeration has no repetitions.

**Definition 1.9 (The finite preimage set).**

$$\forall d \in Bool, n \in \mathrm{Nat}, p \in List\left(\mathrm{Nat}\right),\; Fibre\left(d, n, p\right) = toFinset\left(filter\left((t \mapsto beq\left(SC\left(d, t\right), p\right)), Sn\left(n\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.Fibre` (`✓ std3`).

*Citation.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

List.filter keeps exactly the inputs t for which SC(d,t) equals p; beq denotes the Boolean equality test. Converting to a Finset counts each input once.

**Definition 1.10 (Fibre cardinality).**

$$\forall d \in Bool, n \in \mathrm{Nat}, p \in List\left(\mathrm{Nat}\right),\; F\left(d, n, p\right) = card\left(Fibre\left(d, n, p\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.F` (`✓ std3`).

*Citation.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

The count includes precisely the permutations in the input fibre.

**Definition 1.11 (An attained maximum).**

$$\forall d \in Bool, n \in \mathrm{Nat}, m \in \mathrm{Nat},\; MaximumIs\left(d, n, m\right) \Leftrightarrow \left((\exists p \in List\left(\mathrm{Nat}\right),\; IsPerm\left(n, p\right) \land F\left(d, n, p\right) = m) \land (\forall p \in List\left(\mathrm{Nat}\right),\; IsPerm\left(n, p\right) \Rightarrow F\left(d, n, p\right) \le m)\right)$$

*Formalization.* `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.MaximumIs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value m is attained at an output permutation and bounds every output permutation's fibre size. Both clauses are part of the definition.

**Definition 1.12 (Second-largest distinct fibre size).**

$$\forall n \in \mathrm{Nat}, k \in \mathrm{Nat},\; SecondLargestIs\left(n, k\right) \Leftrightarrow \left((\exists p \in List\left(\mathrm{Nat}\right),\; IsPerm\left(n, p\right) \land F\left(false, n, p\right) = k) \land (\exists m \in \mathrm{Nat},\; k < m \land \left((\exists p \in List\left(\mathrm{Nat}\right),\; IsPerm\left(n, p\right) \land F\left(false, n, p\right) = m) \land (\forall p \in List\left(\mathrm{Nat}\right),\; IsPerm\left(n, p\right) \Rightarrow \left(k < F\left(false, n, p\right) \Rightarrow F\left(false, n, p\right) = m\right))\right))\right)$$

*Formalization.* `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.SecondLargestIs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value k is attained, a larger value m is attained, and every value above k equals m. Thus second-largest refers to distinct values, including zero when it occurs, rather than to a list with repetitions.

**Definition 1.13 (Multiplicity of a fibre size).**

$$\forall n \in \mathrm{Nat}, k \in \mathrm{Nat},\; Multiplicity\left(n, k\right) = length\left(filter\left((p \mapsto beq\left(F\left(false, n, p\right), k\right)), Sn\left(n\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.Multiplicity` (`✓ std3`).

*Citation.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

This counts output permutations p with F(false,n,p)=k. It uses the same repetition-free enumeration Sn(n), including outputs whose fibre is empty.

**Definition 1.14 (Zhao's Conjecture 4.14).**

$$claimMaximum \Leftrightarrow (\forall n \in \mathrm{Nat},\; 2 \le n \Rightarrow \left(MaximumIs\left(false, n, 2^{n - 2}\right) \land MaximumIs\left(true, n, 2^{n - 2}\right)\right))$$

*Formalization.* `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.claimMaximum` (`✓ std3`).

*Citation.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Conjecture 4.14 (arXiv:2410.17057v1, Section 4.1.4, printed page 17) reads: “For n ≥ 2, it holds that max_{π∈𝔖ₙ}|SC₁₂̲₃̲⁻¹(π)| = max_{π∈𝔖ₙ}|SC₃₂̲₁̲⁻¹(π)| = 2ⁿ⁻².” The letters are natural numbers with one-based permutation entries. Stack words are read from top to bottom. The Bool flag false denotes 1-underline(23), and true denotes 3-underline(21). Underlined entries must occupy adjacent positions. The indices i and j in Contains are zero-based Fin values; getElem! is list indexing with default zero, and the bounds ensure that every index used here is valid. Subtraction is natural subtraction, truncated at zero; the conjectures' lower bounds make their exponents ordinary nonnegative differences. The chain of equalities is encoded by the two attained maxima each equalling 2^(n-2), with both conjuncts under the same quantifier and lower bound.

**Definition 1.15 (Zhao's Conjecture 5.2).**

$$claimSecondLargest \Leftrightarrow (\forall n \in \mathrm{Nat},\; 3 \le n \Rightarrow \left(SecondLargestIs\left(n, 2^{n - 3}\right) \land Multiplicity\left(n, 2^{n - 3}\right) = 2 \cdot n - 2\right))$$

*Formalization.* `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.claimSecondLargest` (`✓ std3`).

*Citation.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Conjecture 5.2 (arXiv:2410.17057v1, Section 5, printed page 20) reads: “The second-largest number of preimages under SC₁₂̲₃̲ that a permutation in 𝔖ₙ can have is 2ⁿ⁻³, for n ≥ 3. Furthermore, the number of permutations π ∈ 𝔖ₙ satisfying |SC₁₂̲₃̲⁻¹(π)| = 2ⁿ⁻³ is 2n − 2.” The letters are natural numbers with one-based permutation entries. Stack words are read from top to bottom. The Bool flag false denotes 1-underline(23), and true denotes 3-underline(21). Underlined entries must occupy adjacent positions. The indices i and j in Contains are zero-based Fin values; getElem! is list indexing with default zero, and the bounds ensure that every index used here is valid. Subtraction is natural subtraction, truncated at zero; the conjectures' lower bounds make their exponents ordinary nonnegative differences. The second-largest-value clause and the multiplicity clause are both retained under the same universal quantifier. The carrier 𝔖ₙ is expressed by IsPerm(n,p).

**Theorem 1.16 (The maximum claim is false).**

$$\neg claimMaximum$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.resultMaximum` (`✓ std3`). ∎

*Resolves.* `Problems/zhao-vincular-stack-maximum-preimages-refutation` (refuted) by `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.resultMaximum`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhao-vincular-stack-maximum-preimages-refutation","declaration_gid":"D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.resultMaximum","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

At n=9, 129 explicitly listed distinct permutations map to 765432819 under the false flag. Each mapping and permutation membership is checked separately. The claimed maximum would bound that fibre by 2^7=128, contradicting its cardinality lower bound. An exact maximum for n=9 is not needed.

**Theorem 1.17 (The second-largest claim is false).**

$$\neg claimSecondLargest$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.resultSecondLargest` (`✓ std3`). ∎

*Resolves.* `Problems/zhao-vincular-stack-second-largest-preimages-refutation` (refuted) by `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.resultSecondLargest`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhao-vincular-stack-second-largest-preimages-refutation","declaration_gid":"D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.resultSecondLargest","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Enumeration of all 120 input permutations at n=5 gives F(false,5,32415)=5 and F(false,5,43215)=8. These are distinct fibre values greater than 2^2=4, which contradicts the asserted uniqueness of a larger value. This refutes the conjunction through its first clause; the multiplicity clause is not separately refuted.

## References

- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.Contains`
- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.F`
- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.Fibre`
- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.IsPerm`
- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.MaximumIs`
- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.Multiplicity`
- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.Process`
- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.Push`
- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.SC`
- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.SecondLargestIs`
- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.Sn`
- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.claimMaximum`
- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.claimSecondLargest`
- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.decidableContains`
- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.decidableIsPerm`
- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.resultMaximum`
- Truth anchor: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.resultSecondLargest`
