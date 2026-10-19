# Tărnăuceanu's reciprocal subgroup-order conjecture

## Abstract

The subgroup-order reciprocal sum has no universal lower bound above one on finite non-cyclic groups.

**Definition 1.1 (The reciprocal subgroup-order sum).**

$$\forall G \in Type,\; [Group\left(G\right)] f\left(G\right) = finsum\left(\operatorname{fun} H : Subgroup\left(G\right) \mapsto \frac{1}{\operatorname{Nat.cast}\left(\operatorname{Nat.card}\left(H\right)\right)}\right)$$

*Formalization.* `D5/S3/FiniteGroups/TarnauceanuReciprocalSubgroupOrders.f` (`✓ std3`).

*Citation.* M. Tărnăuceanu (2024). *On the sum of inverses of subgroup orders in finite groups*. URL: <https://www.math.uaic.ro/~martar/pdf/articole/articol%20141.pdf>.

*Commentary.*

The source states on printed p. 116: “In the current note, we consider the function f(G) = Σ_{H∈L(G)} 1/|H|.” Here L(G) is the subgroup lattice, including the trivial subgroup and the whole group. The displayed definition sums the reciprocal real cardinality of every subgroup.

**Definition 1.2 (Conjecture 3.1).**

$$\neg \left(\exists c \in \mathbb{R},\; 1 < c \land \left(\forall G \in Type,\; [Group\left(G\right)] [Finite\left(G\right)] \left(\neg IsCyclic\left(G\right)\right) \Rightarrow c < f\left(G\right)\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/TarnauceanuReciprocalSubgroupOrders.claim` (`✓ std3`).

*Citation.* M. Tărnăuceanu (2024). *On the sum of inverses of subgroup orders in finite groups*. URL: <https://www.math.uaic.ro/~martar/pdf/articole/articol%20141.pdf>.

*Commentary.*

The source states on printed p. 119: “There is no constant c > 1 such that f(G) > c, for all finite non-cyclic groups G.” The Lean statement quantifies over every carrier type with its group and finite instances and expresses the strict inequality using the reciprocal subgroup-order sum.

**Theorem 1.3 (Conjecture 3.1 holds).**

$$\neg \left(\exists c \in \mathbb{R},\; 1 < c \land \left(\forall G \in Type,\; [Group\left(G\right)] [Finite\left(G\right)] \left(\neg IsCyclic\left(G\right)\right) \Rightarrow c < f\left(G\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/TarnauceanuReciprocalSubgroupOrders.result` (`✓ std3`). ∎

*Resolves.* `Problems/tarnauceanu-2024-reciprocal-subgroup-orders` (proved) by `D5/S3/FiniteGroups/TarnauceanuReciprocalSubgroupOrders.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tarnauceanu-2024-reciprocal-subgroup-orders","declaration_gid":"D5/S3/FiniteGroups/TarnauceanuReciprocalSubgroupOrders.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. Tărnăuceanu (2024). *On the sum of inverses of subgroup orders in finite groups*. URL: <https://www.math.uaic.ro/~martar/pdf/articole/articol%20141.pdf>.

*Commentary.*

For any c > 1, choose a large prime q, then a prime p congruent to one modulo q, and finally an exponent s. The frozen split extension of Cyclic p by Cyclic (q^s) is non-cyclic. Its subgroups are inverse images of quotient subgroups, proper embedded quotient subgroups, and conjugates of the full complement. The resulting reciprocal sum is bounded by (1/p)·q/(q−1) + q/(q−1) + p/q^s. Letting q and then s grow makes the excess over one smaller than c−1.

The argument uses the elementary prime supplier for primes congruent to one modulo q and therefore does not assume infinitely many Sophie Germain primes. The proof concerns finite non-cyclic groups and gives no rate statement for the least value at a fixed group order.

## References

- Truth anchor: `D5/S3/FiniteGroups/TarnauceanuReciprocalSubgroupOrders.claim`
- Truth anchor: `D5/S3/FiniteGroups/TarnauceanuReciprocalSubgroupOrders.f`
- Truth anchor: `D5/S3/FiniteGroups/TarnauceanuReciprocalSubgroupOrders.result`
- Dependency: [D5/S3/FiniteGroups/CyclicPrimePowerAction](CyclicPrimePowerAction.md)
