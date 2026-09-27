# Rare-Edge Survival Recurrence

## Abstract

Avoiding paths for the single-peak parity kernel satisfy an exact cubic survival recurrence.

**Definition 1.1 (Avoiding-path survival mass).**

$$s_{T}= \sum_{x: \operatorname{path}(T)} \frac{1}{\lvert X \rvert} \prod_{t<T} \operatorname{P}(x_{t}, x_{t+1}) \mathbf {1}_{\forall t<T, \neg (\operatorname{region}(x_{t})=Z, \operatorname{region}(x_{t+1})=H)}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakRareEdgeSurvival.survival` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The survival mass at time T is the total uniform-start weight of explicit paths x_0, ..., x_T that never traverse an edge from the opposite region Z to the peak region H. Each path weight is the product of the single-peak kernel along its T transitions.

**Theorem 1.2 (Exact survival recurrence).**

$$\operatorname{chi}(x) \in \{\pm 1\}, \operatorname{chi}(z)=1, \lvert X \rvert=2 M, \lvert \{\operatorname{chi}(x)=1\} \rvert=M, M\geq 2, q=\frac{r}{M-1}, p=\frac{1}{2\lvert X \rvert},\quad \varepsilon =1-r \Rightarrow s_{0}=1,\quad s_{1}=1-p,\quad s_{2}=1-2p,\quad \forall T\geq 0, s_{T+3}=s_{T+2}-p \varepsilon s_{T+1}-p r s_{T}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/SinglePeakRareEdgeSurvival.survival_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the sign function takes only the values 1 and -1, the peak has sign 1, the state space has 2M elements with M positive signs, M is at least 2, and q = r/(M-1). Put N = |X|, p = 1/(2N), and epsilon = 1-r, written as varepsilon in the display.

The mass starts at one. One forbidden edge is possible after one step and two placements are possible after two steps, giving s_1 = 1-p and s_2 = 1-2p. For every later horizon, the killed three-region transition operator obeys its cubic identity, yielding the displayed recurrence.

The bridge from state paths to the three-region recursion appends one last state to every path, separates the final transition, and sums its kernel weight over the peak, bulk, and opposite regions.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakRareEdgeSurvival.survival`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakRareEdgeSurvival.survival_recurrence`
- Dependency: [D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent](SinglePeakPathCurrent.md)
