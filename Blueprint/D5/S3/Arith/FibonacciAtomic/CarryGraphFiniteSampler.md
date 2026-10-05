# Finite Carry-slot Sampling

## Abstract

A stationary carry table needs only a bounded slot control to preserve every fair-tape output and charge.

**Definition 1.1 (Bounded active controls).**

$$(\forall m: \mathbb{N}, \operatorname{Active}\left(m\right) = \{(s, j) \in \operatorname{Product}\left(\operatorname{S}\left(m\right), \mathbb{N}\right)\mid j < \operatorname{r}\left(s\right)\})$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler.Active` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

S(m) contains exactly the legal integer carry states. The slot j is a natural number below r, so an active control has positive width. The stored fields are r, e and j; no depth or history word is stored.

**Definition 1.2 (Root control).**

$$(\forall m: \mathbb{N}, (2 \le m \to \operatorname{initial}\left(m\right) = \operatorname{inl}\left((\operatorname{root}\left(m\right), 0)\right)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler.initial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The root has r=1 and e=m, with its unique slot numbered zero.

**Definition 1.3 (One-bit control transition).**

$$(\forall m: \mathbb{N}, (\forall f: \operatorname{P}\left(m\right), (\forall u: Bool, (\forall c: \operatorname{Sum}\left(\operatorname{Active}\left(m\right), \operatorname{Fin}\left(m\right)\right), \operatorname{step}\left(m, f, u, c\right) \in \operatorname{Sum}\left(\operatorname{Active}\left(m\right), \operatorname{Fin}\left(m\right)\right)))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An output control is absorbing. At an active control (s,j), apply the legal action f(s), form the increasing list L of its fixed labels, and set z=2j+toNat(u). If z is below the length of L, output L[z]. Otherwise move to the carry successor and slot z-length(L). A slot guard totalizes the definition by retaining the old active control when the guard fails; the correspondence proves this case is never taken from the root.

**Definition 1.4 (Control and separate invoice).**

$$(\forall m: \mathbb{N}, (\forall f: \operatorname{P}\left(m\right), (\forall c: \operatorname{Sum}\left(\operatorname{Active}\left(m\right), \operatorname{Fin}\left(m\right)\right), (\forall tape: Tape, (\operatorname{execute}\left(m, f, c, tape, 0\right) = (c, 0) \land (\forall d: \mathbb{N}, \operatorname{execute}\left(m, f, c, tape, (d + 1)\right) = (\operatorname{step}\left(m, f, \operatorname{bit}\left(tape, d\right), \operatorname{fst}\left(\operatorname{execute}\left(m, f, c, tape, d\right)\right)\right), (\operatorname{snd}\left(\operatorname{execute}\left(m, f, c, tape, d\right)\right) + \operatorname{indicator}\left(isLeft, \operatorname{fst}\left(\operatorname{execute}\left(m, f, c, tape, d\right)\right)\right)))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler.execute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At an output control, execution returns the previous control and invoice directly. Only the active branch takes the next tape bit and increments the invoice. Only the control and that bit enter step; the invoice is an external execution observation.

**Definition 1.5 (First output with its invoice).**

$$(\forall m: \mathbb{N}, (\forall f: \operatorname{P}\left(m\right), (\forall c: \operatorname{Sum}\left(\operatorname{Active}\left(m\right), \operatorname{Fin}\left(m\right)\right), (\forall tape: Tape, \operatorname{sample}\left(m, f, c, tape\right) = \operatorname{firstOutput}\left(\operatorname{execute}\left(m, f, c, tape\right)\right)))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler.sample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the first execution index whose control is an output, and return its label and invoice. The sample is absent if no finite output occurs.

**Definition 1.6 (Every active step is charged).**

$$(\forall m: \mathbb{N}, (\forall f: \operatorname{P}\left(m\right), (\forall c: \operatorname{Sum}\left(\operatorname{Active}\left(m\right), \operatorname{Fin}\left(m\right)\right), (\forall tape: Tape, \operatorname{bill}\left(m, f, c, tape\right) = \sum_{d \in \mathbb{N}}\operatorname{indicator}\left(isLeft, \operatorname{fst}\left(\operatorname{execute}\left(m, f, c, tape, d\right)\right)\right)))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler.bill` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum is nonnegative extended-real. A divergent execution has infinitely many active steps and therefore an infinite bill.

**Theorem 1.7 (Finite control attains the critical bit bill).**

$$(\forall m: \mathbb{N}, (2 \le m \to ((\exists f: \operatorname{P}\left(m\right), (0 < \operatorname{anchorValue}\left(\operatorname{policyPath}\left(m, f, \operatorname{root}\left(m\right)\right)\right) \land \operatorname{pathCost}\left(\operatorname{policyPath}\left(m, f, \operatorname{root}\left(m\right)\right)\right) = (\operatorname{alpha}\left(m\right) \cdot \operatorname{anchorValue}\left(\operatorname{policyPath}\left(m, f, \operatorname{root}\left(m\right)\right)\right)))) \land (\forall f: \operatorname{P}\left(m\right), (\exists gamma: Path, (\exists p: \operatorname{Fin}\left(m\right) \to \mathbb{R}, (gamma = \operatorname{policyPath}\left(m, f, \operatorname{root}\left(m\right)\right) \land (\forall i: \operatorname{Fin}\left(m\right), \operatorname{p}\left(i\right) = \operatorname{ofDigits}\left(\operatorname{labelDigit}\left(gamma, i\right)\right)) \land (0 < \operatorname{anchorValue}\left(gamma\right) \to (\operatorname{pathCost}\left(gamma\right) = (\operatorname{alpha}\left(m\right) \cdot \operatorname{anchorValue}\left(gamma\right)) \to (\operatorname{IsRootPath}\left(m, gamma\right) \land \operatorname{Finite}\left(\operatorname{Active}\left(m\right)\right) \land \operatorname{card}\left(\operatorname{Active}\left(m\right)\right) \le \frac{(m^{2} \cdot (m - 1))}{2} \land \operatorname{card}\left(\operatorname{Fin}\left(m\right)\right) = m \land (\forall tape: Tape, (\forall d: \mathbb{N}, ((\forall i: \operatorname{Fin}\left(m\right), (\forall n: \mathbb{N}, (\operatorname{scan}\left(m, gamma, tape, d\right) = \operatorname{inl}\left((i, n)\right) \to \operatorname{execute}\left(m, f, \operatorname{initial}\left(m\right), tape, d\right) = (\operatorname{inr}\left(i\right), n)))) \land (\forall j: \mathbb{N}, (\operatorname{scan}\left(m, gamma, tape, d\right) = \operatorname{inr}\left(j\right) \to (\exists x: \operatorname{Active}\left(m\right), (\operatorname{execute}\left(m, f, \operatorname{initial}\left(m\right), tape, d\right) = (\operatorname{inl}\left(x\right), d) \land \operatorname{core}\left(x\right) = \operatorname{state}\left(gamma, d\right) \land \operatorname{slot}\left(x\right) = j))))))) \land (\forall tape: Tape, (\operatorname{sample}\left(m, f, \operatorname{initial}\left(m\right), tape\right) = \operatorname{treeSample}\left(m, gamma, tape\right) \land \operatorname{bill}\left(m, f, \operatorname{initial}\left(m\right), tape\right) = \operatorname{treeBill}\left(m, gamma, tape\right))) \land (\forall i: \operatorname{Fin}\left(m\right), 0 < \operatorname{p}\left(i\right)) \land \sum_{i \in \operatorname{Fin}\left(m\right)}\operatorname{p}\left(i\right) = 1 \land 0 < \operatorname{anchorValue}\left(gamma\right) \land \operatorname{inf}\left(\operatorname{range}\left(p\right)\right) = \operatorname{anchorValue}\left(gamma\right) \land (\forall i: \operatorname{Fin}\left(m\right), (\exists q: \mathbb{Q}, \operatorname{real}\left(q\right) = \operatorname{p}\left(i\right))) \land (\forall i: \operatorname{Fin}\left(m\right), \operatorname{p}\left(i\right) = \sum_{d \in \mathbb{N}}\frac{\operatorname{indicator}\left(\operatorname{labelSet}\left(m, gamma, d\right), i\right)}{2^{(d + 1)}}) \land (\forall tape: Tape, (\forall i: \operatorname{Fin}\left(m\right), (\forall d: \mathbb{N}, \operatorname{sample}\left(m, f, \operatorname{initial}\left(m\right), tape\right) = \operatorname{some}\left((i, (d + 1))\right) \iff (\operatorname{prefix}\left(tape, (d + 1)\right), i) \in \operatorname{stopping}\left(m, gamma, d\right)))) \land (\forall tape: Tape, (\forall i: \operatorname{Fin}\left(m\right), (\forall n: \mathbb{N}, (\operatorname{sample}\left(m, f, \operatorname{initial}\left(m\right), tape\right) = \operatorname{some}\left((i, n)\right) \to \operatorname{bill}\left(m, f, \operatorname{initial}\left(m\right), tape\right) = n)))) \land (\forall i: \operatorname{Fin}\left(m\right), \operatorname{fairTape}\left(\{tape \in Tape\mid (\exists n: \mathbb{N}, \operatorname{sample}\left(m, f, \operatorname{initial}\left(m\right), tape\right) = \operatorname{some}\left((i, n)\right))\}\right) = \operatorname{ofReal}\left(\operatorname{p}\left(i\right)\right)) \land (\forall d: \mathbb{N}, \operatorname{fairTape}\left(\{tape \in Tape\mid (\operatorname{sample}\left(m, f, \operatorname{initial}\left(m\right), tape\right) = none \lor (\exists i: \operatorname{Fin}\left(m\right), (\exists n: \mathbb{N}, (\operatorname{sample}\left(m, f, \operatorname{initial}\left(m\right), tape\right) = \operatorname{some}\left((i, n)\right) \land d < n))))\}\right) = \operatorname{ofReal}\left(\frac{\operatorname{r}\left(\operatorname{state}\left(gamma, d\right)\right)}{2^{d}}\right)) \land (\forall^{\operatorname{ae}\left(fairTape\right)} tape: Tape, (\exists i: \operatorname{Fin}\left(m\right), (\exists n: \mathbb{N}, \operatorname{sample}\left(m, f, \operatorname{initial}\left(m\right), tape\right) = \operatorname{some}\left((i, n)\right)))) \land \operatorname{lintegral}\left(fairTape, \operatorname{bill}\left(m, f, \operatorname{initial}\left(m\right)\right)\right) = \operatorname{ofReal}\left(\operatorname{pathCost}\left(gamma\right)\right) \land \operatorname{pathCost}\left(gamma\right) = \operatorname{cost}\left(p\right) \land \operatorname{cost}\left(p\right) = (\operatorname{alpha}\left(m\right) \cdot \operatorname{anchorValue}\left(gamma\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least two, a critical stationary table with a positive anchor exists. Every stationary table whose positive anchor and path cost satisfy C=alpha(m) times the anchor has a finite slot machine. Its policy path gamma starts at the root, and p is the law obtained from that path's fixed label digits. At every index on every tape, a returned scan label and charge agree with the machine control and invoice; a continuing scan slot agrees with the machine's carry state and slot. Thus their first-return samples and total bills coincide even on exceptional divergent tapes. In the display, core(x) is the stored carry state and slot(x) is its natural slot; treeSample and treeBill denote the existing fixed-label tree sample and bill.

The active-control bound is m squared times (m-1) divided by two, with m additional absorbing output labels. The output law is rational, strictly positive and normalized, its minimum is the positive anchor, its label probabilities are the digit sums, and its stopping tail is r(d)/2 raised to d. It returns almost surely and every returned invoice equals the total bill. The expected bill equals the policy-path cost, the dyadic cost of p and alpha(m) times the anchor.

The finite stationary root orbit repeats a state. Equal tail digit streams at two distinct indices, together with the finite-prefix identity for ofDigits, give a rational expression for each probability. The statement gives no minimum-state claim or uniform bound on the number of bits read.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler.Active`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler.bill`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler.execute`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler.initial`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler.sample`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphFiniteSampler.step`
- Dependency: [D5/S3/Arith/FibonacciAtomic/CarryGraphCriticalAttainment](CarryGraphCriticalAttainment.md)
