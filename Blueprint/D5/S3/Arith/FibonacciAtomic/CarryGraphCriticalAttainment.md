# Carry-graph Critical Attainment

## Abstract

The discounted root price detects the full real slope and yields a positive optimal output law.

**Definition 1.1 (Full real minimum-atom slope).**

$$(\forall m: \mathbb{N}, \operatorname{alpha}\left(m\right) = \operatorname{inf}\left(\{y \in \mathbb{R}\mid (\exists p: \operatorname{Fin}\left(m\right) \to \mathbb{R}, (\exists k: \operatorname{Fin}\left(m\right), ((\forall i: \operatorname{Fin}\left(m\right), 0 < \operatorname{p}\left(i\right)) \land \sum_{i}\operatorname{p}\left(i\right) = 1 \land (\forall i: \operatorname{Fin}\left(m\right), \operatorname{p}\left(k\right) \le \operatorname{p}\left(i\right)) \land y = \frac{\operatorname{cost}\left(p\right)}{\operatorname{p}\left(k\right)})))\}\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphCriticalAttainment.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The infimum ranges over every strictly positive real law of total mass one and every minimizing index. Ties do not change the ratio. The cost is the dyadic floor-tail cost.

**Definition 1.2 (Original-graph Bellman minimum).**

$$(\forall m: \mathbb{N}, (\forall x: \mathbb{R}, (\forall v: \operatorname{S}\left(m\right) \to \mathbb{R}, (\forall s: \operatorname{S}\left(m\right), \operatorname{bellman}\left(m, x, v, s\right) = (\operatorname{r}\left(s\right) + (\frac{1}{2} \cdot \operatorname{inf}\left(\{(\operatorname{v}\left(\operatorname{successor}\left(s, a\right)\right) - (x \cdot \operatorname{b}\left(a\right)))\mid a \in \operatorname{A}\left(m, s\right)\}\right)))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphCriticalAttainment.bellman` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

S(m) is the subtype of the original integer carry states satisfying IsState(m), and A(m,s) is the subtype of actions satisfying Legal(m,s). Every legal action is retained, including actions at unreachable states. The successor is the original carry successor. The price of the anchor bit carries the next-column discount.

**Definition 1.3 (Stationary-table orbit).**

$$(\forall m: \mathbb{N}, (\forall f: \operatorname{P}\left(m\right), (\forall start: \operatorname{S}\left(m\right), (\forall d: \mathbb{N}, (\operatorname{state}\left(\operatorname{policyPath}\left(m, f, start\right), d\right) = \operatorname{iterate}\left(\operatorname{step}\left(f\right), d, start\right) \land \operatorname{action}\left(\operatorname{policyPath}\left(m, f, start\right), d\right) = \operatorname{f}\left(\operatorname{iterate}\left(\operatorname{step}\left(f\right), d, start\right)\right))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CarryGraphCriticalAttainment.policyPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P(m) consists of all dependent tables assigning one legal action to each legal state. The map step(f) sends a state to the successor of its selected action. Its iterate defines the state sequence and the table gives the action sequence.

**Theorem 1.4 (Legal actions exist).**

$$(\forall m: \mathbb{N}, (\forall s: State, (\operatorname{IsState}\left(m, s\right) \to (\exists a: Action, \operatorname{Legal}\left(m, s, a\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/CarryGraphCriticalAttainment.legal_action_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every bounded carry state has a legal action with anchor bit zero. Splitting the required number of one-labels between departing equal labels and larger labels respects both capacities and keeps the successor within the state bounds.

**Theorem 1.5 (Canonical paths of positive laws).**

$$(\forall m: \mathbb{N}, (2 \le m \to (\forall p: \operatorname{Fin}\left(m\right) \to \mathbb{R}, (((\forall i: \operatorname{Fin}\left(m\right), 0 < \operatorname{p}\left(i\right)) \land \sum_{i}\operatorname{p}\left(i\right) = 1) \to (\forall k: \operatorname{Fin}\left(m\right), ((\forall i: \operatorname{Fin}\left(m\right), \operatorname{p}\left(k\right) \le \operatorname{p}\left(i\right)) \to (\exists gamma: Path, (\operatorname{IsRootPath}\left(m, gamma\right) \land \operatorname{anchorValue}\left(gamma\right) = \operatorname{p}\left(k\right) \land \operatorname{pathCost}\left(gamma\right) = \operatorname{cost}\left(p\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/CarryGraphCriticalAttainment.canonical_root_path_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every strictly positive normalized real law and every minimizing index, its dyadic floor columns define a legal path from the original root. The chosen atom is the anchor value, and the residual tail sum is exactly the dyadic cost. These paths compare Bellman root prices with every cost-to-minimum-mass ratio.

**Theorem 1.6 (Root prices and critical attainment).**

$$(\forall m: \mathbb{N}, (2 \le m \to (\exists V: \mathbb{R} \to \operatorname{S}\left(m\right) \to \mathbb{R}, (\exists f: \mathbb{R} \to \operatorname{P}\left(m\right), ((\forall x: \mathbb{R}, (\operatorname{bellman}\left(m, x, \operatorname{V}\left(x\right)\right) = \operatorname{V}\left(x\right) \land (\forall w: \operatorname{S}\left(m\right) \to \mathbb{R}, (\operatorname{bellman}\left(m, x, w\right) = w \to w = \operatorname{V}\left(x\right))))) \land (\forall x: \mathbb{R}, (\forall s: \operatorname{S}\left(m\right), \operatorname{V}\left(x, s\right) = (\operatorname{r}\left(s\right) + (\frac{1}{2} \cdot (\operatorname{V}\left(x, \operatorname{successor}\left(s, \operatorname{f}\left(x, s\right)\right)\right) - (x \cdot \operatorname{b}\left(\operatorname{f}\left(x, s\right)\right))))))) \land (\forall x: \mathbb{R}, (\operatorname{IsRootPath}\left(m, \operatorname{policyPath}\left(m, \operatorname{f}\left(x\right), \operatorname{root}\left(m\right)\right)\right) \land \operatorname{V}\left(x, \operatorname{root}\left(m\right)\right) = (\operatorname{pathCost}\left(\operatorname{policyPath}\left(m, \operatorname{f}\left(x\right), \operatorname{root}\left(m\right)\right)\right) - (x \cdot \operatorname{anchorValue}\left(\operatorname{policyPath}\left(m, \operatorname{f}\left(x\right), \operatorname{root}\left(m\right)\right)\right))) \land (\forall gamma: Path, (\operatorname{IsRootPath}\left(m, gamma\right) \to \operatorname{V}\left(x, \operatorname{root}\left(m\right)\right) \le (\operatorname{pathCost}\left(gamma\right) - (x \cdot \operatorname{anchorValue}\left(gamma\right))))))) \land (\forall x: \mathbb{R}, (0 \le \operatorname{V}\left(x, \operatorname{root}\left(m\right)\right) \iff x \le \operatorname{alpha}\left(m\right))) \land \operatorname{V}\left(\operatorname{alpha}\left(m\right), \operatorname{root}\left(m\right)\right) = 0 \land (0 < \operatorname{anchorValue}\left(\operatorname{policyPath}\left(m, \operatorname{f}\left(\operatorname{alpha}\left(m\right)\right), \operatorname{root}\left(m\right)\right)\right) \land (\forall i: \operatorname{Fin}\left(m\right), 0 < \operatorname{ofDigits}\left(\operatorname{labelDigit}\left(\operatorname{policyPath}\left(m, \operatorname{f}\left(\operatorname{alpha}\left(m\right)\right), \operatorname{root}\left(m\right)\right), i\right)\right)) \land \sum_{i \in \operatorname{Fin}\left(m\right)}\operatorname{ofDigits}\left(\operatorname{labelDigit}\left(\operatorname{policyPath}\left(m, \operatorname{f}\left(\operatorname{alpha}\left(m\right)\right), \operatorname{root}\left(m\right)\right), i\right)\right) = 1 \land \operatorname{inf}\left(\{\operatorname{ofDigits}\left(\operatorname{labelDigit}\left(\operatorname{policyPath}\left(m, \operatorname{f}\left(\operatorname{alpha}\left(m\right)\right), \operatorname{root}\left(m\right)\right), i\right)\right)\mid i \in \operatorname{Fin}\left(m\right)\}\right) = \operatorname{anchorValue}\left(\operatorname{policyPath}\left(m, \operatorname{f}\left(\operatorname{alpha}\left(m\right)\right), \operatorname{root}\left(m\right)\right)\right) \land (\forall^{\operatorname{ae}\left(fairTape\right)} tape: Tape, (\exists i: \operatorname{Fin}\left(m\right), (\exists n: \mathbb{N}, \operatorname{sample}\left(m, \operatorname{policyPath}\left(m, \operatorname{f}\left(\operatorname{alpha}\left(m\right)\right), \operatorname{root}\left(m\right)\right), tape\right) = \operatorname{some}\left((i, n)\right)))) \land (\forall i: \operatorname{Fin}\left(m\right), \operatorname{fairTape}\left(\{tape \in Tape\mid (\exists n: \mathbb{N}, \operatorname{sample}\left(m, \operatorname{policyPath}\left(m, \operatorname{f}\left(\operatorname{alpha}\left(m\right)\right), \operatorname{root}\left(m\right)\right), tape\right) = \operatorname{some}\left((i, n)\right))\}\right) = \operatorname{ofReal}\left(\operatorname{ofDigits}\left(\operatorname{labelDigit}\left(\operatorname{policyPath}\left(m, \operatorname{f}\left(\operatorname{alpha}\left(m\right)\right), \operatorname{root}\left(m\right)\right), i\right)\right)\right)) \land \operatorname{lintegral}\left(fairTape, \operatorname{bill}\left(m, \operatorname{policyPath}\left(m, \operatorname{f}\left(\operatorname{alpha}\left(m\right)\right), \operatorname{root}\left(m\right)\right)\right)\right) = \operatorname{ofReal}\left(\operatorname{pathCost}\left(\operatorname{policyPath}\left(m, \operatorname{f}\left(\operatorname{alpha}\left(m\right)\right), \operatorname{root}\left(m\right)\right)\right)\right) \land \operatorname{pathCost}\left(\operatorname{policyPath}\left(m, \operatorname{f}\left(\operatorname{alpha}\left(m\right)\right), \operatorname{root}\left(m\right)\right)\right) = \operatorname{cost}\left((i: \operatorname{Fin}\left(m\right) \mapsto \operatorname{ofDigits}\left(\operatorname{labelDigit}\left(\operatorname{policyPath}\left(m, \operatorname{f}\left(\operatorname{alpha}\left(m\right)\right), \operatorname{root}\left(m\right)\right), i\right)\right))\right) \land \operatorname{cost}\left((i: \operatorname{Fin}\left(m\right) \mapsto \operatorname{ofDigits}\left(\operatorname{labelDigit}\left(\operatorname{policyPath}\left(m, \operatorname{f}\left(\operatorname{alpha}\left(m\right)\right), \operatorname{root}\left(m\right)\right), i\right)\right))\right) = (\operatorname{alpha}\left(m\right) \cdot \operatorname{anchorValue}\left(\operatorname{policyPath}\left(m, \operatorname{f}\left(\operatorname{alpha}\left(m\right)\right), \operatorname{root}\left(m\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/CarryGraphCriticalAttainment.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m>=2 there are value functions and deterministic legal tables for all real prices. Each value is the unique finite Bellman fixed point on every state, and each table attains the one-step minimum at every state. The root is o=(1,m). The selected stationary root path attains the minimum over all legal root paths, not merely an infimum.

The root is nonnegative exactly at prices at most alpha(m). At the critical price it is zero. The critical table has a positive anchor. Its fixed-label tree, given by labelDigit, sample and bill, returns a strictly positive normalized real law, with minimum mass equal to that anchor. It stops almost surely, has that return law under the independent fair bit tape, and its expected charged bill equals both the whole-column path cost and the dyadic cost. These costs equal alpha(m) times the anchor.

Finite legal actions supply statewise minimum selectors. The half-discount fixed point comes from the finite Bellman contraction. Summing the one-step inequalities telescopes the discounted value sequence; bounded state values make the tail vanish. The inequalities are equalities along the selected table, so the root path attains the full path minimum.

Canonical paths of positive real laws compare the root price with every cost-to-minimum-mass ratio. Arbitrarily close ratios to the infimum give root values smaller than epsilon/m at the critical price, so that value is zero without assuming attainment. The root path cost is at least one, which rules out a zero anchor. Its actual output law then gives alpha times the anchor at most the dyadic cost, at most the path cost, with both endpoints equal. This forces all costs to agree.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphCriticalAttainment.alpha`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphCriticalAttainment.bellman`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphCriticalAttainment.canonical_root_path_exists`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphCriticalAttainment.legal_action_exists`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphCriticalAttainment.policyPath`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CarryGraphCriticalAttainment.result`
- Dependency: [D5/S1/Digit/RadixFloorDigit](../../../S1/Digit/RadixFloorDigit.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/CarryGraphRealization](CarryGraphRealization.md)
- Dependency: [D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality](../../Observer/DynamicProgramming/StationaryPolicyOptimality.md)
