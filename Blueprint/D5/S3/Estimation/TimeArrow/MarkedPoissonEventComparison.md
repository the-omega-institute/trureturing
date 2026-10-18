# Actual Marked Counts and Poisson Events

## Abstract

Actual Marked Counts and Poisson Events

**Theorem 1.1 (Forward count tails).**

$$\forall M,q,s,k:Nat, \forall r:Real, \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), {1\leq q \land q<M \land 0<r \land r<1 \land \operatorname{compensation}(M, q, r)<1 \land \operatorname{injective}(m) \land (k=1 \lor k=2) \land 64\leq M \land \frac{s}{{M}^{2}}\leq \frac{1}{256}} \Rightarrow \forall e:\operatorname{Experiment}(), \forall B:Nat, \operatorname{forwardTotalTail}(r, S, m, s, e, B)+\operatorname{directionalPoissonTotalTail}(r, S, m, \frac{s}{(2) \cdot (M)}, B)\leq \frac{(3) \cdot (\operatorname{exp}((k) \cdot (\frac{s}{(2) \cdot (M)})))}{{2}^{B}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/MarkedPoissonEventComparison.actual_forward_marked_count_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward actual total-count tail plus the genuine product-Poisson tail at rates L(1+b(m(j)))/2 and L(1-b(m(j)))/2 is at most 3 exp(kL)/2^B. Both experiments share the same support and arbitrary integer s. The assumptions are M>=64, 1<=q<M, 0<r<1, compensation<1, distinct one or two marks, and s/M^2<=1/256.

**Theorem 1.2 (Forward count events).**

$$\forall kappa,Czero:Real, {0<kappa \land kappa<1 \land 1\leq Czero} \Rightarrow \exists A:Real, \exists Mzero:Nat, \exists etazero:Real, 0<A \land 64\leq Mzero \land 0<etazero \land \forall M,q,s,k:Nat, \forall r:Real, \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), {1\leq q \land q<M \land 0<r \land r\leq 1-kappa \land \operatorname{compensation}(M, q, r)\leq 1-kappa \land \operatorname{injective}(m) \land (k=1 \lor k=2) \land Mzero\leq M \land 1\leq \frac{s}{(2) \cdot (M)} \land \frac{\frac{s}{(2) \cdot (M)}}{M}\leq etazero} \Rightarrow \forall e:\operatorname{Experiment}(), \forall B:Nat, {B\leq (Czero) \cdot (\frac{s}{(2) \cdot (M)})} \Rightarrow \forall E:\operatorname{Set}(\operatorname{Sum}(\operatorname{Fin}(k), \operatorname{Fin}(k))\to Nat), \lvert \operatorname{forwardEvent}(r, S, m, s, e, E)-\operatorname{directionalPoissonEvent}(r, S, m, \frac{s}{(2) \cdot (M)}, E) \rvert\leq (\frac{(A) \cdot ({\frac{s}{(2) \cdot (M)}}^{k+1})}{M}) \cdot (\operatorname{directionalPoissonEvent}(r, S, m, \frac{s}{(2) \cdot (M)}, E))+\frac{(3) \cdot (\operatorname{exp}((k) \cdot (\frac{s}{(2) \cdot (M)})))}{{2}^{B}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/MarkedPoissonEventComparison.actual_forward_marked_every_event` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed 0<kappa<1 and Czero>=1, choose constants A>0, Mzero>=64 and etazero>0 before the support, marks, experiment, tuple cutoff and event. Assume r<=1-kappa and compensation<=1-kappa. The scale L=s/(2M) is real, L>=1 and L/M<=etazero. The same fixed support defines both actual history mass and directional exact Poisson rates. Every count event has absolute discrepancy at most A L^(k+1)/M times its comparison mass plus 3 exp(kL)/2^B, whenever B<=Czero L.

**Definition 1.3 (poissonProduct).**

$$\forall iota:Type, [\operatorname{Fintype}(iota)] \forall mu:iota\to \operatorname{NonnegativeReal}(), \operatorname{poissonProduct}(mu)=\operatorname{productPoissonMeasures}(mu)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/MarkedPoissonEventComparison.poissonProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite coordinate type iota and nonnegative rates mu, poissonProduct(mu) is the product of the genuine Poisson probability measures on the natural numbers. It contains all count tuples, without truncation.

**Theorem 1.4 (product poisson tail).**

$$\forall iota:Type, [\operatorname{Fintype}(iota)] \forall mu:iota\to \operatorname{NonnegativeReal}(), \forall B:Nat, \operatorname{productPoissonTotalTail}(mu, B)\leq \frac{\operatorname{exp}(\operatorname{sum}(mu))}{{2}^{B}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/MarkedPoissonEventComparison.product_poisson_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The total-count tail is at most exp(sum_i mu(i))/2^B for every natural B, including zero rates. The proof evaluates the coordinate exponential series at tilt 2, forms the product integral and applies Markov inequality.

**Theorem 1.5 (actual reverse marked count tail).**

$$\forall M,q,s,k:Nat, \forall r:Real, \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), {1\leq q \land q<M \land 0<r \land r<1 \land \operatorname{compensation}(M, q, r)<1 \land \operatorname{injective}(m) \land (k=1 \lor k=2) \land 64\leq M \land \frac{s}{{M}^{2}}\leq \frac{1}{256}} \Rightarrow \forall e:\operatorname{Experiment}(), \forall B:Nat, \operatorname{reverseTotalTail}(r, S, m, s, e, B)+\operatorname{fairPoissonTotalTail}(k, \frac{s}{(2) \cdot (M)}, B)\leq \frac{(3) \cdot (\operatorname{exp}((k) \cdot (\frac{s}{(2) \cdot (M)})))}{{2}^{B}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/MarkedPoissonEventComparison.actual_reverse_marked_count_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

L=s/(2M), and all 2k comparison rates are exactly L/2. The actual term sums reverse history masses with total marked count greater than B. The comparison term is the tail of the genuine product Poisson law. For M>=64 and s/M^2<=1/256 their sum is at most 3 exp(kL)/2^B, uniformly over the same fixed support, distinct marks and both experiments.

**Theorem 1.6 (actual reverse marked every event).**

$$\forall Czero:Real, {1\leq Czero} \Rightarrow \exists A:Real, \exists Mzero:Nat, \exists etazero:Real, 0<A \land 64\leq Mzero \land 0<etazero \land \forall M,q,s,k:Nat, \forall r:Real, \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), {1\leq q \land q<M \land 0<r \land r<1 \land \operatorname{compensation}(M, q, r)<1 \land \operatorname{injective}(m) \land (k=1 \lor k=2) \land Mzero\leq M \land 1\leq \frac{s}{(2) \cdot (M)} \land \frac{\frac{s}{(2) \cdot (M)}}{M}\leq etazero} \Rightarrow \forall e:\operatorname{Experiment}(), \forall B:Nat, {B\leq (Czero) \cdot (\frac{s}{(2) \cdot (M)})} \Rightarrow \forall E:\operatorname{Set}(\operatorname{Sum}(\operatorname{Fin}(k), \operatorname{Fin}(k))\to Nat), \lvert \operatorname{reverseEvent}(r, S, m, s, e, E)-\operatorname{fairPoissonEvent}(k, \frac{s}{(2) \cdot (M)}, E) \rvert\leq (\frac{(A) \cdot ({\frac{s}{(2) \cdot (M)}}^{k+1})}{M}) \cdot (\operatorname{fairPoissonEvent}(k, \frac{s}{(2) \cdot (M)}, E))+\frac{(3) \cdot (\operatorname{exp}((k) \cdot (\frac{s}{(2) \cdot (M)})))}{{2}^{B}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/MarkedPoissonEventComparison.actual_reverse_marked_every_event` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Czero>=1 there exist A>0, Mzero>=64 and etazero>0. Whenever L=s/(2M)>=1, L/M<=etazero and k=1 or 2, every natural B<=Czero L and every count event E satisfy the displayed bound. The count vector uses two copies of Fin(k), one per destination parity. ReverseEvent sums actual reverse history masses whose vector belongs to E. nu is the independent Poisson product with all rates L/2. The relative term is A L^(k+1)/M times nu(E); the additive term is 3 exp(kL)/2^B. Local estimates are summed on the finite total-count box, and both tails control its complement.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonEventComparison.actual_forward_marked_count_tail`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonEventComparison.actual_forward_marked_every_event`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonEventComparison.actual_reverse_marked_count_tail`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonEventComparison.actual_reverse_marked_every_event`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonEventComparison.poissonProduct`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonEventComparison.product_poisson_tail`
- Dependency: [D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath](ActualReverseMarkedPath.md)
- Dependency: [D5/S3/Estimation/TimeArrow/ArbitraryMarkedCountPoissonRelative](ArbitraryMarkedCountPoissonRelative.md)
