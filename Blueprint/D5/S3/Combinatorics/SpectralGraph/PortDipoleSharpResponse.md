# Sharp dipole response at two prescribed moments

## Abstract

The sharp zero-shift response of a unit dipole with two prescribed moments on finite connected conductance graphs.

A real symmetric matrix L with zero row sums and nonpositive off-diagonal entries is the conductance Laplacian. Edge ij is present when −Lᵢⱼ > 0. With d = eᵢ − eⱼ and distinct terminals, the exact moments are p = dᵀLd/2 and q = ‖Ld‖²/2. Unit current solves Lu = d, so the effective resistance is uᵢ − uⱼ and the normalized dipole response is (uᵢ − uⱼ)/2. Dörfler and Bullo supply the electrical-network model. The moment-constrained proof here derives two energy bounds and an exact-moment family approaching their maximum.

**Theorem 1.1 (Unit current on connected support).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PortDipoleSharpResponse.exists_current_solution`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PortDipoleSharpResponse.exists_current_solution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Florian Dörfler; Francesco Bullo (2013). *Kron Reduction of Graphs With Applications to Electrical Networks*. DOI: [10.1109/TCSI.2012.2215780](https://doi.org/10.1109/TCSI.2012.2215780). URL: <https://arxiv.org/abs/1102.2950>.

*Commentary.*

On any finite carrier with connected positive-conductance support, every terminal pair i, j admits a solution of Lu = d. For f = d/√2, every w satisfying Lw = f has fᵀw = (uᵢ − uⱼ)/2. The energy identity and connectedness force the kernel to consist of constants, so the zero-sum dipole belongs to the range. This theorem also allows i = j.

**Theorem 1.2 (Two-moment lower bound on any finite carrier).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PortDipoleSharpResponse.response_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PortDipoleSharpResponse.response_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct terminals and a unit-current solution, assume the two moment equalities, p > 0 and q < 4p². The normalized response is at least B = max{1/p, 2p/(4p² − q)}, and is strictly larger when q > p². The proof tests the electrical energy first with the dipole and then with a vector supported on the two terminals and weighted by their Laplacian entries. The equality conditions give strictness.

**Theorem 1.3 (Sharp infimum over connected conductance graphs).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PortDipoleSharpResponse.isGLB_responses`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PortDipoleSharpResponse.isGLB_responses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For p > 0 and p² ≤ q < 4p², B is the greatest lower bound of normalized responses over all finite connected positive-conductance supports with distinct terminals and both moments prescribed exactly. The resistance infimum is 2B. At q = p² a single edge of conductance p/2 realizes B. For q > p² a four-vertex graph has a three-edge path with conductances x, M, y and an optional direct terminal edge of conductance t. The moment identities are independent of M. With x and y positive and t ≥ 0 chosen for the prescribed p and q, the normalized response approaches B as M grows.

**Theorem 1.4 (Attainment at zero variance).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PortDipoleSharpResponse.infimum_mem_responses_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PortDipoleSharpResponse.infimum_mem_responses_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same moment hypotheses, B belongs to the set of normalized responses exactly when q = p². Equivalently, the resistance infimum is attained precisely at zero dipole variance. The single-edge realization gives attainment at the endpoint, and the strict lower bound rules it out at positive variance.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PortDipoleSharpResponse.exists_current_solution`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PortDipoleSharpResponse.infimum_mem_responses_iff`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PortDipoleSharpResponse.isGLB_responses`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PortDipoleSharpResponse.response_lower_bound`
