# Weighted pure rays and stochastic transport

## Abstract

A unitary stochastic transport permutes weighted pure rays. For the fixed five effects, the grouped weights force a scalar phase and determine every stochastic kernel.

**Theorem 1.1 (All autonomous kernels for the fixed five effects).**

$$\forall U \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(5\right), \operatorname{Fin}\left(5\right), \mathbb{R}\right),\; \left(T \in \operatorname{colStochastic}\left(\mathbb{R}, \operatorname{Fin}\left(5\right)\right) \land \left(\forall r \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{PosSemidef}\left(r\right) \Rightarrow \left(\operatorname{trace}\left(r\right) = 1 \Rightarrow \operatorname{mulVec}\left(T, \operatorname{probability}\left(r\right)\right) = \operatorname{probability}\left((U: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)) \cdot r \cdot \operatorname{star}\left((U: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))\right)\right)\right)\right)\right) \Leftrightarrow \left(\left(\exists g \in \mathbb{R},\; (U: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)) = (\operatorname{exp}\left((g: \mathbb{C}) \cdot \operatorname{Complex.I}\right)) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)))\right) \land \left(\exists t \in \mathbb{R},\; 0 \le t \land \left(t \le \frac{1}{3} \land T = \operatorname{kernel}\left(t\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/WeightedRayStochasticRigidity.original_five_effect_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The outcome order is (0,2,3,5,25). The Pauli Y convention has upper-right entry -i. The gain is the positive reciprocal of 1+2 sqrt(3)+sqrt(11). The effects are E25=(gain/2)(sqrt(3) I-X-Y-Z), E0=3 E25, E2=(gain/2)(sqrt(11) I+3X+Y+Z), E3=gain(I+Z), and E5=(gain/2)(sqrt(11) I+X+3Y+Z). Probability is the real trace of rho times the corresponding effect.

Autonomy quantifies over every positive semidefinite trace-one qubit matrix, with one real five-by-five matrix acting on the probability column. Every entry is nonnegative and every column sums to one. The matrix can depend on the specified unitary but is fixed across all input states.

The real span of density matrices is the Hermitian matrix space, by all_density_tomographically_complete. Applying the trace functional to the difference of the two Hermitian effect expressions therefore turns equality on every density matrix into the operator transport identity. The pure projections use blochMatrix and its public pure-projection theorem. Their positive weights in the fixed order are gain times (3 sqrt(3), sqrt(11), 2, sqrt(11), sqrt(3)).

The common permutation and grouped conservation theorem applies to this same unitary and matrix. The four total weights are gain times (4 sqrt(3), sqrt(11), 2, sqrt(11)). Since 4 sqrt(3)>sqrt(11)>2, groups A and C are fixed. Commutation with C's projector makes the unitary diagonal. Commutation with A's projector, whose off-diagonal entry is nonzero, makes its two diagonal entries equal. Unitarity makes this scalar have norm one; Complex.norm_eq_one_iff gives its real phase.

Every ray is then fixed. The support constraint fixes each of the three singleton columns and confines columns 0 and 25 to their common group. Set t=T25,0. Column sums and the stationary weight ratio (3,1) give T00=1-t, T0,25=3t, and T25,25=1-3t. Entry nonnegativity is exactly 0<=t<=1/3. Conversely these matrices preserve the relation p0=3 p25, and a scalar phase preserves every density matrix. The kernel rows are (1-t,0,0,0,3t), (0,1,0,0,0), (0,0,1,0,0), (0,0,0,1,0), and (t,0,0,0,1-3t). Both endpoints belong to the classification.

No stochastic inverse or invertibility is assumed. The result classifies this fixed Born probability representation; it supplies no unknown actual event laws, physical availability of inputs, acquisition, calibration, or origin of Born probabilities.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/WeightedRayStochasticRigidity.original_five_effect_classification`
- Dependency: [D5/S3/Quantum/Information/ActualQubitChordObstruction](../Information/ActualQubitChordObstruction.md)
- Dependency: [D5/S3/Quantum/Measurement/AntidistinguishabilityGram](AntidistinguishabilityGram.md)
- Dependency: [D5/S3/Quantum/Measurement/FourQubitParentConstruction](FourQubitParentConstruction.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
