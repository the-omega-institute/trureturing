# Fixed-label Carry-tree Execution

## Abstract

Fixed one-label intervals determine ordered children and an actual bit-by-bit scan.

**Definition 1.1 (Fixed labels).**

$$(\forall m: \mathbb{N}, (\forall gamma: Path, (\forall d: \mathbb{N}, (\forall i: \operatorname{Fin}\left(m\right), i \in \operatorname{labelSet}\left(m, gamma, d\right) \iff ((\operatorname{b}\left(\operatorname{action}\left(gamma, d\right)\right) = 1 \land i < \operatorname{e}\left(\operatorname{state}\left(gamma, d\right)\right) + \operatorname{c}\left(\operatorname{action}\left(gamma, d\right)\right)) \lor (\operatorname{b}\left(\operatorname{action}\left(gamma, d\right)\right) \neq 1 \land \operatorname{e}\left(\operatorname{state}\left(gamma, d\right)\right) - \operatorname{h}\left(\operatorname{action}\left(gamma, d\right)\right) \le i \land i < \operatorname{e}\left(\operatorname{state}\left(gamma, d\right)\right) + \operatorname{c}\left(\operatorname{action}\left(gamma, d\right)\right)))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.labelSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Indices are zero-based. On an anchor-one column the selected labels start at zero. On an anchor-zero column they start at e-h and stop before e+c.

**Definition 1.2 (Output digits).**

$$(\forall m: \mathbb{N}, (\forall gamma: Path, (\forall i: \operatorname{Fin}\left(m\right), (\forall d: \mathbb{N}, \operatorname{labelDigit}\left(gamma, i, d\right) = \operatorname{indicator}\left(\operatorname{labelSet}\left(m, gamma, d\right), i\right)))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.labelDigit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Membership in the selected set gives digit one; every other label has digit zero.

**Definition 1.3 (Charged scan).**

$$(\forall m: \mathbb{N}, (\forall gamma: Path, (\forall tape: Tape, (\forall d: \mathbb{N}, \operatorname{scan}\left(m, gamma, tape, d\right) \in \operatorname{Sum}\left(\operatorname{Product}\left(\operatorname{Fin}\left(m\right), \mathbb{N}\right), \mathbb{N}\right)))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.scan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The root is active slot zero. At depth d an active slot j reads tape(d), forms z=2j+toNat(tape(d)), and returns the z-th column label with charge d+1 if z is below the label count. Otherwise it continues in slot z minus that count. A returned state stays unchanged and reads no further bits.

**Definition 1.4 (Ordered children).**

$$(\forall words: \operatorname{List}\left(\operatorname{List}\left(Bool\right)\right), \operatorname{children}\left(words\right) = \operatorname{flatMap}\left((w \mapsto [\operatorname{append}\left(w, [false]\right), \operatorname{append}\left(w, [true]\right)]), words\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.children` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each word contributes first its false child and then its true child, preserving parent order.

**Definition 1.5 (Continuing words).**

$$(\forall m: \mathbb{N}, (\forall gamma: Path, (\forall d: \mathbb{N}, \operatorname{continuing}\left(m, gamma, d + 1\right) = \operatorname{drop}\left(\operatorname{length}\left(\operatorname{sort}\left(\operatorname{labelSet}\left(m, gamma, d\right)\right)\right), \operatorname{children}\left(\operatorname{continuing}\left(m, gamma, d\right)\right)\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.continuing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Depth zero consists of the empty word. Every later level expands the continuing parents and removes the initial children assigned to labels.

**Definition 1.6 (Labelled stopping words).**

$$(\forall m: \mathbb{N}, (\forall gamma: Path, (\forall d: \mathbb{N}, \operatorname{stopping}\left(m, gamma, d\right) = \operatorname{zip}\left(\operatorname{children}\left(\operatorname{continuing}\left(m, gamma, d\right)\right), \operatorname{sort}\left(\operatorname{labelSet}\left(m, gamma, d\right)\right)\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.stopping` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected initial children are paired with the increasing output labels. The zip has the shorter of the two input lengths.

**Definition 1.7 (First return).**

$$(\forall m: \mathbb{N}, (\forall gamma: Path, (\forall tape: Tape, \operatorname{sample}\left(m, gamma, tape\right) = \operatorname{firstLeft}\left(\operatorname{scan}\left(m, gamma, tape\right)\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.sample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sample is the first left scan state, with its output label and charged length. It is absent on tapes with no finite return.

**Definition 1.8 (Total charged reads).**

$$(\forall m: \mathbb{N}, (\forall gamma: Path, (\forall tape: Tape, \operatorname{bill}\left(m, gamma, tape\right) = \sum_{d \in \mathbb{N}}\operatorname{indicator}\left(isRight, \operatorname{scan}\left(m, gamma, tape, d\right)\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.bill` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nonnegative extended-real sum counts one read for each active scan state. It is infinite on an execution that remains active forever.

**Theorem 1.9 (Every root path has its actual fair-bit tree).**

$$(\forall m: \mathbb{N}, (2 \le m \to (\forall gamma: Path, (\operatorname{IsRootPath}\left(m, gamma\right) \to ((\forall i: \operatorname{Fin}\left(m\right), 0 \le \operatorname{ofDigits}\left(\operatorname{labelDigit}\left(gamma, i\right)\right)) \land \sum_{i \in \operatorname{Fin}\left(m\right)}\operatorname{ofDigits}\left(\operatorname{labelDigit}\left(gamma, i\right)\right) = 1 \land \operatorname{ofDigits}\left(\operatorname{labelDigit}\left(gamma, 0\right)\right) = \operatorname{anchorValue}\left(gamma\right) \land (\forall i: \operatorname{Fin}\left(m\right), \operatorname{anchorValue}\left(gamma\right) \le \operatorname{ofDigits}\left(\operatorname{labelDigit}\left(gamma, i\right)\right)) \land (0 < \operatorname{anchorValue}\left(gamma\right) \to (\forall i: \operatorname{Fin}\left(m\right), 0 < \operatorname{ofDigits}\left(\operatorname{labelDigit}\left(gamma, i\right)\right))) \land \operatorname{IsPrefixFree}\left(\{w \in \operatorname{List}\left(Bool\right)\mid(\exists d: \mathbb{N}, (\exists i: \operatorname{Fin}\left(m\right), (w, i) \in \operatorname{stopping}\left(m, gamma, d\right)))\}\right) \land (\forall d: \mathbb{N}, (\operatorname{map}\left(snd, \operatorname{stopping}\left(m, gamma, d\right)\right) = \operatorname{sort}\left(\operatorname{labelSet}\left(m, gamma, d\right)\right) \land (\forall w: \operatorname{Product}\left(\operatorname{List}\left(Bool\right), \operatorname{Fin}\left(m\right)\right), (w \in \operatorname{stopping}\left(m, gamma, d\right) \to \operatorname{length}\left(\operatorname{fst}\left(w\right)\right) = d + 1)))) \land (\forall tape: Tape, (\forall i: \operatorname{Fin}\left(m\right), (\forall d: \mathbb{N}, \operatorname{sample}\left(m, gamma, tape\right) = \operatorname{some}\left((i, d + 1)\right) \iff (\operatorname{prefix}\left(tape, d + 1\right), i) \in \operatorname{stopping}\left(m, gamma, d\right)))) \land (\forall tape: Tape, (\forall i: \operatorname{Fin}\left(m\right), (\forall n: \mathbb{N}, (\operatorname{sample}\left(m, gamma, tape\right) = \operatorname{some}\left((i, n)\right) \to \operatorname{bill}\left(m, gamma, tape\right) = n)))) \land (\forall i: \operatorname{Fin}\left(m\right), (\operatorname{MeasurableSet}\left(\{tape \in Tape\mid(\exists n: \mathbb{N}, \operatorname{sample}\left(m, gamma, tape\right) = \operatorname{some}\left((i, n)\right))\}\right) \land \operatorname{fairTape}\left(\{tape \in Tape\mid(\exists n: \mathbb{N}, \operatorname{sample}\left(m, gamma, tape\right) = \operatorname{some}\left((i, n)\right))\}\right) = \operatorname{ofReal}\left(\operatorname{ofDigits}\left(\operatorname{labelDigit}\left(gamma, i\right)\right)\right))) \land (\forall d: \mathbb{N}, (\operatorname{MeasurableSet}\left(\{tape \in Tape\mid(\operatorname{sample}\left(m, gamma, tape\right) = none \lor (\exists i: \operatorname{Fin}\left(m\right), (\exists n: \mathbb{N}, (\operatorname{sample}\left(m, gamma, tape\right) = \operatorname{some}\left((i, n)\right) \land d < n))))\}\right) \land \operatorname{fairTape}\left(\{tape \in Tape\mid(\operatorname{sample}\left(m, gamma, tape\right) = none \lor (\exists i: \operatorname{Fin}\left(m\right), (\exists n: \mathbb{N}, (\operatorname{sample}\left(m, gamma, tape\right) = \operatorname{some}\left((i, n)\right) \land d < n))))\}\right) = \operatorname{ofReal}\left(\frac{\operatorname{r}\left(\operatorname{state}\left(gamma, d\right)\right)}{2^{d}}\right))) \land (\forall^{\operatorname{ae}\left(fairTape\right)} tape: Tape, (\exists i: \operatorname{Fin}\left(m\right), (\exists n: \mathbb{N}, \operatorname{sample}\left(m, gamma, tape\right) = \operatorname{some}\left((i, n)\right)))) \land \operatorname{lintegral}\left(fairTape, \operatorname{bill}\left(m, gamma\right)\right) = \operatorname{ofReal}\left(\operatorname{pathCost}\left(gamma\right)\right) \land \operatorname{pathCost}\left(gamma\right) \le m \land \operatorname{cost}\left((i: \operatorname{Fin}\left(m\right) \mapsto \operatorname{ofDigits}\left(\operatorname{labelDigit}\left(gamma, i\right)\right))\right) \le \operatorname{pathCost}\left(gamma\right) \land (\exists delta: Path, (\operatorname{IsRootPath}\left(2, delta\right) \land \operatorname{cost}\left((i: \operatorname{Fin}\left(2\right) \mapsto \operatorname{ofDigits}\left(\operatorname{labelDigit}\left(delta, i\right)\right))\right) < \operatorname{pathCost}\left(delta\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least two and every legal root path, the fixed digits give a nonnegative normalized law. Index zero is the minimum anchor and equals its digit series; a positive anchor makes every label positive.

The constructed stopping words are prefix-free and carry exactly the selected labels at each depth. The first-return sample outputs a label and length exactly when its tape prefix is that labelled leaf. Its bill is that length, so each consumed fair bit is charged once. Under the existing independent fair-tape measure its label law is the digit law, its stopping tail is r(d)/2^d, and it returns almost surely. The expected bill equals pathCost, is at most m, and dominates the existing dyadic cost. No canonical-expansion, rationality or computability hypothesis is added.

The inequality can be strict. For two labels, take the root action (b,h,c)=(0,1,0) and then repeat (1,0,0) at state (1,1). The output digits are 0.01111... and 0.10000..., so both probabilities are one half. The path cost is two while the dyadic cost of its law is one.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.bill`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.children`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.continuing`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.labelDigit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.labelSet`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.sample`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.scan`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.stopping`
- Dependency: [D5/S0/Computability/Coding/PrefixFreeCode](../../../S0/Computability/Coding/PrefixFreeCode.md)
- Dependency: [D5/S0/Tower/DBonacci/TerminalSampling](../../../S0/Tower/DBonacci/TerminalSampling.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding](CarryGraphEmbedding.md)
