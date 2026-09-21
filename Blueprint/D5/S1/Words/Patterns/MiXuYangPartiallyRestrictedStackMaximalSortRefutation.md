# A Counterexample to the Maximal-Sort Characterization

## Abstract

Mi, Xu and Yang's Conjecture 5.2 is false at n=3 for the permutation 132.

The stack is listed from top to bottom. The paper's map s_(T,k) reads input from left to right, pushes when the proposed stack remains (T,k)-avoiding, and otherwise emits the top and retries the same input. The remaining stack is emitted top-first. West's s is the instance with T={21}, k=0, while t is the instance with T={12,21}, k=1.

**Definition 1.1 (Pattern containment).**

$$\forall pi \in \operatorname{List}\left(\mathrm{Nat}\right), sigma \in \operatorname{List}\left(\mathrm{Nat}\right),\; (\operatorname{Contains}\left(pi, sigma\right)) \Leftrightarrow ((\exists u \in \operatorname{List}\left(\mathrm{Nat}\right),\; (u \in \operatorname{sublists}\left(pi\right)) \land ((\operatorname{length}\left(u\right) = \operatorname{length}\left(sigma\right)) \land (\forall i \in \mathrm{Nat}, j \in \mathrm{Nat},\; ((i < \operatorname{length}\left(u\right)) \land (j < \operatorname{length}\left(u\right))) \Rightarrow ((getElem!\left(u, i\right) < getElem!\left(u, j\right)) \Leftrightarrow (getElem!\left(sigma, i\right) < getElem!\left(sigma, j\right)))))))$$

*Formalization.* `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.Contains` (`✓ std3`).

*Citation.* Jared Mi; Jeffrey Xu; Jason Yang (2025). *Partially Restricted Stacks as Functions*. DOI: [10.54550/ECA2025V5S3R22](https://doi.org/10.54550/ECA2025V5S3R22). URL: <https://ecajournal.haifa.ac.il/Volume2025/ECA2025_S2A22.pdf>.

*Commentary.*

A finite Boolean scan of the subsequences backs this Prop definition. Equal length and agreement of every strict-order comparison express order-isomorphism. This is the containment definition on printed page 2.

**Definition 1.2 (Partially restricted avoidance).**

$$\forall T \in \operatorname{List}\left(\operatorname{List}\left(\mathrm{Nat}\right)\right), k \in \mathrm{Nat}, w \in \operatorname{List}\left(\mathrm{Nat}\right),\; (\operatorname{TkAvoiding}\left(T, k, w\right)) \Leftrightarrow (\lvert\{sigma \in T \mid \operatorname{Contains}\left(w, sigma\right)\}\rvert \le k)$$

*Formalization.* `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.TkAvoiding` (`✓ std3`).

*Citation.* Jared Mi; Jeffrey Xu; Jason Yang (2025). *Partially Restricted Stacks as Functions*. DOI: [10.54550/ECA2025V5S3R22](https://doi.org/10.54550/ECA2025V5S3R22). URL: <https://ecajournal.haifa.ac.il/Volume2025/ECA2025_S2A22.pdf>.

*Commentary.*

T is read as the set of its distinct members, following the paper's phrase 'k distinct permutations from T' on printed page 1. The displayed cardinality is the number of distinct members of T contained in w, and it is at most k. This is the (T,k)-avoiding definition on printed page 2.

**Definition 1.3 (The partially restricted stack map).**

$$\begin{aligned}\forall T \in \operatorname{List}\left(\operatorname{List}\left(\mathrm{Nat}\right)\right), k \in \mathrm{Nat}, x \in \mathrm{Nat},\; \operatorname{pushInput}\left(T, k, x, []\right) = ([], [x])\\\forall T \in \operatorname{List}\left(\operatorname{List}\left(\mathrm{Nat}\right)\right), k \in \mathrm{Nat}, x \in \mathrm{Nat}, a \in \mathrm{Nat}, rest \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{pushInput}\left(T, k, x, \operatorname{cons}\left(a, rest\right)\right) = \operatorname{if}\left(\operatorname{TkAvoiding}\left(T, k, \operatorname{cons}\left(x, \operatorname{cons}\left(a, rest\right)\right)\right), ([], \operatorname{cons}\left(x, \operatorname{cons}\left(a, rest\right)\right)), (\operatorname{cons}\left(a, \operatorname{fst}\left(\operatorname{pushInput}\left(T, k, x, rest\right)\right)\right), \operatorname{snd}\left(\operatorname{pushInput}\left(T, k, x, rest\right)\right))\right)\\\forall T \in \operatorname{List}\left(\operatorname{List}\left(\mathrm{Nat}\right)\right), k \in \mathrm{Nat}, stack \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{stackRun}\left(T, k, stack, []\right) = stack\\\forall T \in \operatorname{List}\left(\operatorname{List}\left(\mathrm{Nat}\right)\right), k \in \mathrm{Nat}, stack \in \operatorname{List}\left(\mathrm{Nat}\right), x \in \mathrm{Nat}, xs \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{stackRun}\left(T, k, stack, \operatorname{cons}\left(x, xs\right)\right) = \operatorname{append}\left(\operatorname{fst}\left(\operatorname{pushInput}\left(T, k, x, stack\right)\right), \operatorname{stackRun}\left(T, k, \operatorname{snd}\left(\operatorname{pushInput}\left(T, k, x, stack\right)\right), xs\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.stackRun` (`✓ std3`).

*Citation.* Jared Mi; Jeffrey Xu; Jason Yang (2025). *Partially Restricted Stacks as Functions*. DOI: [10.54550/ECA2025V5S3R22](https://doi.org/10.54550/ECA2025V5S3R22). URL: <https://ecajournal.haifa.ac.il/Volume2025/ECA2025_S2A22.pdf>.

*Commentary.*

The private data function pushInput either pushes x and emits nothing, or emits the current top and recursively retries x against the remaining stack. stackRun drains the top-first stack when the input is empty. These equations implement the push, pop-and-retry, and flush rules on printed page 1. The mirror's s_(T,k) is the page-1 machine for pattern families whose members have length at least two, which covers s and t. With a length-one pattern, the paper leaves the empty-stack pop case undefined.

**Definition 1.4 (West's stack map).**

$$\forall pi \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{s}\left(pi\right) = \operatorname{stackRun}\left([[2, 1]], 0, [], pi\right)$$

*Formalization.* `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.s` (`✓ std3`).

*Citation.* Jared Mi; Jeffrey Xu; Jason Yang (2025). *Partially Restricted Stacks as Functions*. DOI: [10.54550/ECA2025V5S3R22](https://doi.org/10.54550/ECA2025V5S3R22). URL: <https://ecajournal.haifa.ac.il/Volume2025/ECA2025_S2A22.pdf>.

*Commentary.*

The singleton restriction list [21] with allowance zero makes the top-first stack avoid 21, exactly the paper's description of West's s on printed page 1.

**Definition 1.5 (The map t).**

$$\forall pi \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{t}\left(pi\right) = \operatorname{stackRun}\left([[1, 2], [2, 1]], 1, [], pi\right)$$

*Formalization.* `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.t` (`✓ std3`).

*Citation.* Jared Mi; Jeffrey Xu; Jason Yang (2025). *Partially Restricted Stacks as Functions*. DOI: [10.54550/ECA2025V5S3R22](https://doi.org/10.54550/ECA2025V5S3R22). URL: <https://ecajournal.haifa.ac.il/Volume2025/ECA2025_S2A22.pdf>.

*Commentary.*

The restriction list is [12,21] and the allowance is one, matching the notation t=s_({12,21},1) introduced on printed page 2.

**Definition 1.6 (Exact sorting time).**

$$\forall pi \in \operatorname{List}\left(\mathrm{Nat}\right), j \in \mathrm{Nat},\; (\operatorname{TakesSorts}\left(pi, j\right)) \Leftrightarrow ((\operatorname{iterate}\left(\operatorname{compose}\left(s, t\right), j, pi\right) = range'\left(1, \operatorname{length}\left(pi\right)\right)) \land (\forall i \in \mathrm{Nat},\; (i < j) \Rightarrow (\operatorname{iterate}\left(\operatorname{compose}\left(s, t\right), i, pi\right) \ne range'\left(1, \operatorname{length}\left(pi\right)\right))))$$

*Formalization.* `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.TakesSorts` (`✓ std3`).

*Citation.* Jared Mi; Jeffrey Xu; Jason Yang (2025). *Partially Restricted Stacks as Functions*. DOI: [10.54550/ECA2025V5S3R22](https://doi.org/10.54550/ECA2025V5S3R22). URL: <https://ecajournal.haifa.ac.il/Volume2025/ECA2025_S2A22.pdf>.

*Commentary.*

iterate(f,j,pi) denotes the j-th iterate of f at pi. The first clause reaches the identity word of the same length, and the second clause excludes every earlier iterate. The rendered range' notation denotes Lean's List.range'. Thus j is the smallest nonnegative sorting time from printed page 6.

**Definition 1.7 (The proposed extremal form).**

$$\forall n \in \mathrm{Nat}, pi \in \operatorname{List}\left(\mathrm{Nat}\right),\; (\operatorname{LemmaForm}\left(n, pi\right)) \Leftrightarrow (\exists sigma \in \operatorname{List}\left(\mathrm{Nat}\right),\; (pi = \operatorname{cons}\left(2, \operatorname{append}\left(sigma, [1, n]\right)\right)) \land ((\operatorname{Perm}\left(sigma, range'\left(3, n - 3\right)\right)) \land (\neg \operatorname{Contains}\left(sigma, [2, 1, 3]\right))))$$

*Formalization.* `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.LemmaForm` (`✓ std3`).

*Citation.* Jared Mi; Jeffrey Xu; Jason Yang (2025). *Partially Restricted Stacks as Functions*. DOI: [10.54550/ECA2025V5S3R22](https://doi.org/10.54550/ECA2025V5S3R22). URL: <https://ecajournal.haifa.ac.il/Volume2025/ECA2025_S2A22.pdf>.

*Commentary.*

The middle word sigma permutes the entries 3 through n-1 and avoids the pattern 213. The full word begins with 2 and ends with 1,n, as in printed page 7.

**Definition 1.8 (Mi-Xu-Yang Conjecture 5.2).**

$$(claim) \Leftrightarrow ((\forall n \in \mathrm{Nat},\; (3 \le n) \Rightarrow (\forall pi \in \operatorname{List}\left(\mathrm{Nat}\right),\; (\operatorname{Perm}\left(pi, range'\left(1, n\right)\right)) \Rightarrow ((\operatorname{TakesSorts}\left(pi, 2 \cdot n - 5\right)) \Leftrightarrow (\operatorname{LemmaForm}\left(n, pi\right))))))$$

*Formalization.* `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.claim` (`✓ std3`).

*Citation.* Jared Mi; Jeffrey Xu; Jason Yang (2025). *Partially Restricted Stacks as Functions*. DOI: [10.54550/ECA2025V5S3R22](https://doi.org/10.54550/ECA2025V5S3R22). URL: <https://ecajournal.haifa.ac.il/Volume2025/ECA2025_S2A22.pdf>.

*Commentary.*

For every n at least 3 and every permutation pi of the one-based identity word, the asserted equivalence identifies sorting time 2n-5 with the proposed 2 sigma 1 n form. Natural subtraction is truncated at zero; the lower bound makes both displayed differences ordinary nonnegative differences.

**Theorem 1.9 (The conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jared Mi; Jeffrey Xu; Jason Yang (2025). *Partially Restricted Stacks as Functions*. DOI: [10.54550/ECA2025V5S3R22](https://doi.org/10.54550/ECA2025V5S3R22). URL: <https://ecajournal.haifa.ac.il/Volume2025/ECA2025_S2A22.pdf>.

*Commentary.*

At n=3, t sends 132 to 321 and s sends 321 to 123. Thus 132 takes exactly one sort, which equals 2*3-5, but it cannot begin with 2 and so cannot have the form 2 sigma 1 3. This refutes the only-if direction.

## References

- Truth anchor: `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.Contains`
- Truth anchor: `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.LemmaForm`
- Truth anchor: `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.TakesSorts`
- Truth anchor: `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.TkAvoiding`
- Truth anchor: `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.claim`
- Truth anchor: `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.result`
- Truth anchor: `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.s`
- Truth anchor: `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.stackRun`
- Truth anchor: `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.t`
