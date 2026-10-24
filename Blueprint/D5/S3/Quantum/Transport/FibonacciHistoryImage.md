# Native Fibonacci History Images

## Abstract

Every native Fibonacci carry image obeys the complete Fibonacci and golden-power bounds, with an all-point interior realization.

**Theorem 1.1 (Native integer layers and strict interior realization).**

$$\forall d: \mathbb{N}, \forall N: \mathbb{N}, 2 \le d \Rightarrow \forall a: \operatorname{A}\left(d\right), (\forall j: \mathbb{N}, \operatorname{int}\left(\operatorname{k}\left(d, a, j\right)\right) = \lfloor\operatorname{L}\left(j + 2, \operatorname{z}\left(d, a\right)\right)\rfloor - \lfloor\operatorname{L}\left(j, \operatorname{z}\left(d, a\right)\right)\rfloor - \lfloor\operatorname{L}\left(j + 1, \operatorname{z}\left(d, a\right)\right)\rfloor) \land (\operatorname{s}\left(d, N, a\right) = \operatorname{h}\left(N, \operatorname{z}\left(d, a\right)\right)) \land (\exists w: \mathbb{R}^{2}, ((0 < \operatorname{fst}\left(w\right)) \land (\operatorname{fst}\left(w\right) < 1) \land (0 < \operatorname{snd}\left(w\right)) \land (\operatorname{snd}\left(w\right) < 1)) \land (\forall m: \mathbb{N}, m < N + 2 \Rightarrow (\lfloor\operatorname{L}\left(m, w\right)\rfloor = \lfloor\operatorname{L}\left(m, \operatorname{z}\left(d, a\right)\right)\rfloor) \land (0 < \operatorname{fract}\left(\operatorname{L}\left(m, w\right)\right))) \land (\operatorname{s}\left(d, N, a\right) = \operatorname{h}\left(N, w\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/FibonacciHistoryImage.native_history_interior_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A(d)=ZMod(d) times ZMod(d), with each residue represented by its canonical natural value in [0,d). The existing Fibonacci permutation is f(a,b)=(b,a+b) modulo d. Its j-fold native iteration is lowTrajectory d j. The actual carry at time j is the sum of the two canonical representatives at that time divided by d using natural division. The word s(d,N,a)=carryPrefix d N a records every position j<N, including the unique empty word when N=0.

Write z(d,a)=normalizedState d a for (val(a0)/d,val(a1)/d). On real pairs, step(x,y)=(y,x+y), and L(m,z)=linearLayer m z is the first coordinate of its m-fold unquotiented iteration. Thus L(0,z)=x, L(1,z)=y and L(m+2,z)=L(m,z)+L(m+1,z). For m>0 the existing Fibonacci iteration formulas give L(m,z)=F(m-1)x+F(m)y. Define h(N,z)=layerHistory N z by taking, at each j<N, the natural part of floor(L(j+2,z))-floor(L(j,z))-floor(L(j+1,z)).

The first conclusion identifies every actual integer carry with that integer floor difference at the normalized native state. The notation int(k) is the integer embedding of the natural carry. No truncation is hidden in this equality. The second conclusion identifies the complete native word with h. The third constructs a point w in (0,1) times (0,1) at which all floors with m<N+2 agree with those at z(d,a), every corresponding fractional part is strictly positive, and the entire word is still the actual native word.

The quotient calculation uses the native modular iteration and the existing Fibonacci step. Each canonical coordinate is the corresponding unquotiented natural coordinate modulo d, while the floor of its normalized real value is the natural quotient. Adding the two coordinates gives the quotient recurrence with the actual carry as its remainder contribution. This proves the integer-layer identity at every time, including an exact integer layer.

For the interior construction, move both real coordinates by the same positive amount t. The change in L(m,z) is t times L(m,(1,1)), and this coefficient is strictly positive. There are only N+2 relevant layers. Each has a positive distance to its next integer, even when its current value is an integer. The pinned finite-separation theorem Order.exists_between_finsets, applied between {0} and the finite set of scaled next-integer and upper-seam distances, supplies a single t below them all. Every floor stays fixed, every relevant layer becomes strictly larger than its old floor, and both coordinates lie strictly between zero and one.

All d>=2, all natural N, and all canonical states are included. Points on coordinate seams, open edges and simultaneous integer layers use the same positive perturbation argument. The point w is a real point and need not be another modulus-d grid point. This result places the native image inside the interior real-history image; it does not count that image and does not establish a Fibonacci upper bound on its cardinality.

**Theorem 1.2 (The complete native image bound).**

$$\forall d: \mathbb{N}, \forall N: \mathbb{N}, 2 \le d \Rightarrow (\operatorname{Finite}\left(\operatorname{im}\left(\operatorname{s}\left(d, N\right)\right)\right)) \land (\operatorname{card}\left(\operatorname{im}\left(\operatorname{s}\left(d, N\right)\right)\right) \le 4 \times (\operatorname{F}\left(N + 5\right) - N - 4)) \land (\operatorname{natreal}\left(4 \times (\operatorname{F}\left(N + 5\right) - N - 4)\right) \le 4 \times \frac{1 + \operatorname{sqrt}\left(5\right)}{2}^{N + 4}) \land (\operatorname{natreal}\left(\operatorname{F}\left(N + 5\right) - N - 4\right) = \operatorname{natreal}\left(\operatorname{F}\left(N + 5\right)\right) - \operatorname{natreal}\left(N\right) - 4)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/FibonacciHistoryImage.native_history_image_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The image is taken over every state in A(d), with the actual native word s(d,N,a) defined above. It is finite. F is Nat.fib, with F(0)=0, F(1)=1 and the Fibonacci recurrence. The first displayed subtraction is natural subtraction. The notation natreal denotes the real embedding of a natural number; the final equality identifies that subtraction with ordinary real subtraction. The golden constant in the second inequality is exactly (1+sqrt(5))/2.

First replace each native history by its strict interior realization. For each m from 1 to N+1, the condition floor(L(m,w))=k(m) gives a strip between two parallel lines. The strip has positive vertical coefficient F(m). Divide by that coefficient and write its lower and upper boundaries as l(m)-r(m)x and u(m)-r(m)x. The m=1 strip is exactly 0<y<1.

Move to the leftmost feasible abscissa, retaining closed strip inequalities and x>=0. This abscissa is the maximum of zero and the finitely many lower-upper crossing abscissae whose lower slope exceeds the upper slope. The original strict point lies to its right. Choose the largest lower boundary there. If every upper boundary is still strict, the abscissa is zero, so the chosen point lies on the vertical coordinate layer and an active lower layer. Otherwise choose the active lower boundary with least slope and the active upper boundary with greatest slope. Their slopes are strictly separated.

The chosen corner and its unordered pair of integer layers determine every original floor. In the second case, use the midpoint of the two selected slopes: at an integer layer whose slope is below that midpoint the original floor is the corner floor minus one, and at every other layer it is the corner floor. The extremal active slopes prove this rule, including simultaneous intersections. In the vertical-boundary case every original floor is already the corner floor. Applying the floor second difference reconstructs the whole original word, so the native image is contained in the image of these corner codes.

For layers i<j, map the corner to the real circle modulo one in each coordinate and apply the i-fold Fibonacci step. Its first coordinate is zero. The existing iterate_first and iterate_second formulas on the natural pair (0,1) transport to the circle pair through (a,b) mapped to (a times t,b times t), using natural scalar multiplication and Function.Semiconj.iterate_right. They identify the next j-i iterates with consecutive Fibonacci multiples, so the j-th layer says that the second coordinate is killed by F(j-i). The step is injective on the circle pair, and the pinned AddCircle torsion theorem bounds these possibilities by F(j-i). The corner has x in [0,1) and y in [0,1]; one extra bit distinguishes the two representatives on the horizontal seam. Thus the number of corner codes is at most twice the sum of F(j-i) over 0<=i<j<N+2.

The finite sum equals F(N+5)-N-4. Reverse each inner sum with Finset.sum_range_reflect and apply Nat.fib_succ_eq_succ_sum: each row sum plus one equals F(j+2). Sum these equalities, then apply the same pinned partial-sum theorem again after removing the F(0) and F(1) terms. This gives the double sum plus N+4 equal to F(N+5), with no additional recurrence induction. Its natural subtraction is nonnegative, and the proof supplies the exact real-cast identity displayed below. These finite-separation, orbit-transport and sum helpers are consumed applications of closed suppliers and contribute no independent new mathematical content. The corner estimate is stronger than the stated factor-four bound; weakening its factor two to four gives the original inequality. The pinned golden-ratio Fibonacci identity, the Fibonacci recurrence and phi>=1 give F(N+5)<=phi^(N+4), which yields the second inequality.

There is no arrangement-count, orientation or floor-law assumption. The argument covers all d>=2, every natural N, every canonical grid state, coordinate seams, open edges and vertices. At N=0 the word is the unique empty function and the same proof applies. The conclusion is an image-cardinality upper bound for complete one-sided histories. It asserts neither optimality nor a physical acquisition procedure.

## References

- Truth anchor: `D5/S3/Quantum/Transport/FibonacciHistoryImage.native_history_image_bound`
- Truth anchor: `D5/S3/Quantum/Transport/FibonacciHistoryImage.native_history_interior_realization`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling](../../Arith/FibonacciAtomic/GlobalGcdSampling.md)
- Dependency: [D5/S3/Quantum/Transport/FibonacciPrefix](FibonacciPrefix.md)
