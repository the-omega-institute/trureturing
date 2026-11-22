# No uniform bath multiplicity cap for a fixed qutrit

## Abstract

For every positive finite bath multiplicity cap, a finite Gibbs bath realizes a thermal operation of the same qutrit outside the pointwise closure of the real convex hull of the capped class.

**Theorem 1.1 (A Fibonacci bath separates each finite cap).**

Lean statement: `D5/S3/QuantumChannels/ThermalDegeneracyNoUniformCap.no_uniform_bath_cap`

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/ThermalDegeneracyNoUniformCap.no_uniform_bath_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2022). *Which bath Hamiltonians matter for thermal operations?*. DOI: [10.1063/5.0117534](https://doi.org/10.1063/5.0117534). URL: <https://arxiv.org/abs/2207.11189v4>.

*Commentary.*

Fix the qutrit energies at 0, 1 and 2 and the inverse temperature at log 2. The bath has a nonempty finite energy basis with arbitrary real energies e(a). Prepare it independently in the Gibbs state with diagonal weights exp(−log(2) e(a)) divided by their sum. Conjugate the tensor product by a joint unitary commuting with the total Hamiltonian, then trace out the bath. The cap M bounds the number of bath basis vectors at each energy.

Use the same input with diagonal populations (0, 2/3, 1/3) and observe the real part of the ground diagonal entry. For each real bath energy t, the shell capacity is the smaller of the ground multiplicity g(t) and the total excited multiplicity g(t − 1) + g(t − 2). Group bath energies by their fractional part and start each chain at its least energy. Truncating the Fibonacci response at M bounds each chain's Gibbs-weighted partition sum in terms of the weighted deficit from shell capacity. The first M + 1 Fibonacci terms and the geometric tail with multiplicity M give an upper bound independent of the chain length.

For the witness, take levels 0 through M + 8 with multiplicity Fib(j + 1) at level j. A permutation swaps each positive-energy ground basis vector with a distinct excited vector of the same total energy. The unique ground basis vector at level zero stays fixed. The resulting ground population strictly exceeds the bound. The real ground entry at the fixed input is real-linear and continuous in the pointwise topology on matrix maps. Its sublevel set is convex and closed, so the bound holds on the pointwise closure of the real convex hull of the capped class.

Equation (1) and the bath degeneracy question in Section V of Frederik vom Ende's arXiv:2207.11189v4 provide the setting. The Library note also credits the higher-dimensional obstruction from Musat and Rørdam's factorization result and explains how arbitrary finite bath spectra can realize the earlier qutrit examples for a single maximally mixed matrix ancilla.

## References

- Truth anchor: `D5/S3/QuantumChannels/ThermalDegeneracyNoUniformCap.no_uniform_bath_cap`
- Dependency: [D5/S3/QuantumChannels/ThermalOperationDegeneracyRefutation](ThermalOperationDegeneracyRefutation.md)
