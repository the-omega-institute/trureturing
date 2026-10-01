# A three-qubit violation of Cabello's argument beyond 9/64

## Abstract

A genuinely entangled three-qubit state with rational amplitudes, measured with sigma_z and with an observable whose eigenvectors are (3, 4)/5 and (-4, 3)/5 on every qubit, satisfies the three vanishing conditions of Cabello's argument with Q > 0 and gives C = P - Q = 3209679/22562500, which exceeds 9/64. This refutes the conjecture of J. L. Cereceda (arXiv:1609.04763) that 9/64 is the maximum of C over all three-qubit states and local observables.

**Definition 1.1 (The amplitude of a product vector).**

$$\operatorname{amp}\left(a, b, c, \psi\right) = \sum_{i} \sum_{j} \sum_{k} \overline{a_{i}} \cdot \overline{b_{j}} \cdot \overline{c_{k}} \cdot \psi_{ijk}$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.amp` (`✓ std3`).

*Citation.* José L. Cereceda (2017). *Cabello's nonlocality for generalized three-qubit GHZ states*. DOI: [10.1007/s40509-016-0093-7](https://doi.org/10.1007/s40509-016-0093-7). URL: <https://arxiv.org/abs/1609.04763v2>.

*Commentary.*

For vectors a, b, c of C^2 and a three-qubit vector psi, given by its coordinates psi_ijk with i, j, k in Fin 2, amp(a, b, c, psi) is the inner product of a tensor b tensor c with psi, where the bar is complex conjugation (star in Lean).

**Definition 1.2 (The joint probability).**

$$\operatorname{prob}\left(a, b, c, \psi\right) = \left|\operatorname{amp}\left(a, b, c, \psi\right)\right|^{2}$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.prob` (`✓ std3`).

*Citation.* José L. Cereceda (2017). *Cabello's nonlocality for generalized three-qubit GHZ states*. DOI: [10.1007/s40509-016-0093-7](https://doi.org/10.1007/s40509-016-0093-7). URL: <https://arxiv.org/abs/1609.04763v2>.

*Commentary.*

For a unit vector psi, prob(a, b, c, psi) is the probability of the three outcomes whose eigenvectors are a, b and c, the squared modulus of the amplitude (Complex.normSq in Lean).

**Definition 1.3 (Local observables).**

$$\operatorname{IsONB}\left(e, f\right) \Leftrightarrow ((\sum_{i} \overline{e_{i}} \cdot e_{i} = 1) \land \left((\sum_{i} \overline{f_{i}} \cdot f_{i} = 1) \land \sum_{i} \overline{e_{i}} \cdot f_{i} = 0\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.IsONB` (`✓ std3`).

*Citation.* José L. Cereceda (2017). *Cabello's nonlocality for generalized three-qubit GHZ states*. DOI: [10.1007/s40509-016-0093-7](https://doi.org/10.1007/s40509-016-0093-7). URL: <https://arxiv.org/abs/1609.04763v2>.

*Commentary.*

A plus-or-minus-one valued projective qubit observable is given by its eigenvectors e for the outcome +1 and f for the outcome -1, which form an orthonormal basis of C^2.

**Definition 1.4 (Product across the first cut).**

$$\operatorname{ProductCut1}\left(\psi\right) \Leftrightarrow (\exists a, b, \forall i, j, k, \psi_{ijk} = a_{i} \cdot b_{jk})$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.ProductCut1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* José L. Cereceda (2017). *Cabello's nonlocality for generalized three-qubit GHZ states*. DOI: [10.1007/s40509-016-0093-7](https://doi.org/10.1007/s40509-016-0093-7). URL: <https://arxiv.org/abs/1609.04763v2>.

*Commentary.*

psi is a product across the cut separating qubit 1 from qubits 2 and 3 when psi_ijk = a_i b_jk for some a and b.

**Definition 1.5 (Product across the second cut).**

$$\operatorname{ProductCut2}\left(\psi\right) \Leftrightarrow (\exists a, b, \forall i, j, k, \psi_{ijk} = a_{j} \cdot b_{ik})$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.ProductCut2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* José L. Cereceda (2017). *Cabello's nonlocality for generalized three-qubit GHZ states*. DOI: [10.1007/s40509-016-0093-7](https://doi.org/10.1007/s40509-016-0093-7). URL: <https://arxiv.org/abs/1609.04763v2>.

*Commentary.*

psi is a product across the cut separating qubit 2 from qubits 1 and 3 when psi_ijk = a_j b_ik for some a and b.

**Definition 1.6 (Product across the third cut).**

$$\operatorname{ProductCut3}\left(\psi\right) \Leftrightarrow (\exists a, b, \forall i, j, k, \psi_{ijk} = a_{k} \cdot b_{ij})$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.ProductCut3` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* José L. Cereceda (2017). *Cabello's nonlocality for generalized three-qubit GHZ states*. DOI: [10.1007/s40509-016-0093-7](https://doi.org/10.1007/s40509-016-0093-7). URL: <https://arxiv.org/abs/1609.04763v2>.

*Commentary.*

psi is a product across the cut separating qubit 3 from qubits 1 and 2 when psi_ijk = a_k b_ij for some a and b.

**Definition 1.7 (Genuine entanglement).**

$$\operatorname{GenuinelyEntangled}\left(\psi\right) \Leftrightarrow ((\neg\operatorname{ProductCut1}\left(\psi\right)) \land \left((\neg\operatorname{ProductCut2}\left(\psi\right)) \land \neg\operatorname{ProductCut3}\left(\psi\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.GenuinelyEntangled` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* José L. Cereceda (2017). *Cabello's nonlocality for generalized three-qubit GHZ states*. DOI: [10.1007/s40509-016-0093-7](https://doi.org/10.1007/s40509-016-0093-7). URL: <https://arxiv.org/abs/1609.04763v2>.

*Commentary.*

psi is genuinely entangled when it is a product across none of the three cuts. The claim below assumes it, which only weakens the claim: the paper states the conjecture over all possible states and, in its conclusions, over all entangled states.

**Definition 1.8 (The conjecture).**

$$claim \Leftrightarrow (\forall \psi, up, um, dp, dm, (\sum_{i} \sum_{j} \sum_{k} \left|\psi_{ijk}\right|^{2} = 1, \operatorname{GenuinelyEntangled}\left(\psi\right), \forall k, \operatorname{IsONB}\left(\operatorname{up}\left(k\right), \operatorname{um}\left(k\right)\right), \forall k, \operatorname{IsONB}\left(\operatorname{dp}\left(k\right), \operatorname{dm}\left(k\right)\right), \operatorname{prob}\left(\operatorname{dp}\left(0\right), \operatorname{up}\left(1\right), \operatorname{up}\left(2\right), \psi\right) = 0, \operatorname{prob}\left(\operatorname{up}\left(0\right), \operatorname{dp}\left(1\right), \operatorname{up}\left(2\right), \psi\right) = 0, \operatorname{prob}\left(\operatorname{up}\left(0\right), \operatorname{up}\left(1\right), \operatorname{dp}\left(2\right), \psi\right) = 0, 0 < \operatorname{prob}\left(\operatorname{dm}\left(0\right), \operatorname{dm}\left(1\right), \operatorname{dm}\left(2\right), \psi\right)) \Rightarrow \operatorname{prob}\left(\operatorname{up}\left(0\right), \operatorname{up}\left(1\right), \operatorname{up}\left(2\right), \psi\right) - \operatorname{prob}\left(\operatorname{dm}\left(0\right), \operatorname{dm}\left(1\right), \operatorname{dm}\left(2\right), \psi\right) \le \frac{9}{64})$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.claim` (`✓ std3`).

*Citation.* José L. Cereceda (2017). *Cabello's nonlocality for generalized three-qubit GHZ states*. DOI: [10.1007/s40509-016-0093-7](https://doi.org/10.1007/s40509-016-0093-7). URL: <https://arxiv.org/abs/1609.04763v2>.

*Commentary.*

For every genuinely entangled unit vector psi and all observables U_k, D_k on the qubits k = 1, 2, 3, with eigenvectors up(k), um(k) and dp(k), dm(k), if P(D_1,U_2,U_3|+++) = P(U_1,D_2,U_3|+++) = P(U_1,U_2,D_3|+++) = 0 and Q = P(D_1,D_2,D_3|---) > 0, then C = P(U_1,U_2,U_3|+++) - Q is at most 9/64. The paper conjectures that 9/64 is the maximum of C under these conditions, which contains this bound. In Lean the qubits are indexed by Fin 3 from 0.

**Theorem 1.9 (A state beyond 9/64).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/cereceda-2017-three-qubit-cabello-maximum` (refuted) by `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cereceda-2017-three-qubit-cabello-maximum","declaration_gid":"D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* José L. Cereceda (2017). *Cabello's nonlocality for generalized three-qubit GHZ states*. DOI: [10.1007/s40509-016-0093-7](https://doi.org/10.1007/s40509-016-0093-7). URL: <https://arxiv.org/abs/1609.04763v2>.

*Commentary.*

Take U_k = sigma_z, with eigenvectors (1, 0) and (0, 1), and D_k with eigenvectors (3, 4)/5 and (-4, 3)/5 on every qubit, and psi = (16|000> - 12(|001> + |010> + |100>) - 15(|011> + |101> + |110>) + 9|111>)/38, a unit vector since 16^2 + 3 * 12^2 + 3 * 15^2 + 9^2 = 38^2. Each constraint amplitude is (3 * 16 - 4 * 12)/(5 * 38) = 0. P = (16/38)^2 = 64/361, the amplitude of D_1 D_2 D_3 with outcomes - is -889/4750, so Q = 790321/22562500 > 0, and C = 3209679/22562500, which exceeds 9/64 by 589239/361000000. psi is genuinely entangled: across each cut a 2 x 2 determinant of its coordinates is (16 * (-15) - (-12) * (-12))/38^2, not 0. The sums are evaluated by norm_num.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.GenuinelyEntangled`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.IsONB`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.ProductCut1`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.ProductCut2`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.ProductCut3`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.amp`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.prob`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.result`
