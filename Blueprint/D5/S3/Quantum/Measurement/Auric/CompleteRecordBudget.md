# Sharp coherent record information at a fixed labeled law

## Abstract

Sharp coherent record information at a fixed labeled law

**Theorem 1.1 (The exact entropy budget for unequal coordinate capacities).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/CompleteRecordBudget.complete_record_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/CompleteRecordBudget.complete_record_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information*. DOI: [10.1017/9781316848142](https://doi.org/10.1017/9781316848142).

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Acknowledgement.* Chi-Kwong Li and Yiu-Tung Poon (2003). *Principal Submatrices of a Hermitian Matrix*. DOI: [10.1080/0308108031000069164](https://doi.org/10.1080/0308108031000069164). URL: <https://doi.org/10.1080/0308108031000069164>.

*Acknowledgement.* Pedro G. Massey (2010). *Non-commutative Schur–Horn theorems and extended majorization for Hermitian matrices*. DOI: [10.1080/03081080802677615](https://doi.org/10.1080/03081080802677615). URL: <https://arxiv.org/abs/0712.2246>.

*Acknowledgement.* The Omega Institute (2026). *AURIC FIB environment instruments and terminal record memory*. URL: <https://api.github.com/repos/the-omega-institute/trureturing-source-theories/git/blobs/b5cf23ff96f30a7e7345ee983c6d1a51544ec507>.

*Acknowledgement.* The Omega Institute (2026). *AURIC FIB 环境实测记录的 Shannon 熵率*. URL: <https://api.github.com/repos/the-omega-institute/trureturing-source-theories/git/blobs/9a9a0846680dd2fa84c73a2f50ec665d5cdd2674>.

*Commentary.*

Fix three labeled coordinate fibers of capacities m_j in an N-dimensional system and a rank 1 ≤ r ≤ N. The inputs are ρ = P/r for Hermitian rank-r projections P with fiber trace r q_j and constant diagonal within each fiber. Such a state exists exactly when q_j ≥ 0, r q_j ≤ m_j for every j, and Σ_j q_j = 1. An empty fiber requires q_j = 0.

Take d = min(r, N − r). Use t_j = r q_j and f(x) = −x log x in the direct branch, including a tie. Use t_j = m_j − r q_j and f(x) = −(1 − x) log(1 − x) in the complementary branch. The working traces describe the projection frame. The record law remains q in both branches. The gain range is the set of spectral scores divided by r for positive d-dimensional effects summing to I, with traces t_j and ranks bounded by m_j.

Let ℓ_j = (d − m_j)₊ and h₂ be binary entropy in nats. At d = 0 the certificate value B is zero. If the deficits exceed d, the two small capacities give B = m_i h₂(t_i/m_i) + m_k h₂(t_k/m_k). With fitted deficits, a saturated row j gives B = ℓ_j h₂(t_i/ℓ_j) for a different label i. A zero row j gives B = L h₂((t_i − ℓ_k)/L), with L = d − ℓ_i − ℓ_k for the two remaining labels. Terms with zero multiplying dimension contribute zero.

For strict traces with fitted deficits, missing-label columns have multiplicities ℓ_j and the unrestricted column has multiplicity d − Σ_j ℓ_j. A certificate uses proportional weights on the allowed rows in the direct branch and clipped entries max(0, 1 − w_j k_c) in the complementary branch. Columns sum to one and weighted row sums equal the given t_j. The value B is the corresponding multiplicity-weighted sum of f. Every feasible law admits a certificate, and all valid certificates give the same greatest score.

For the actual coherent joint state ω = WρW†, one admissible input simultaneously attains the greatest pinching gain B/r, greatest I(S:R) = H(q) + B/r, and least S(R|S) = −B/r. Here H(q) is the Shannon entropy of the original record in nats. Orthogonal projective recording gives the pinched system marginal and diag(q) as the record marginal. The joint entropy is S(ρ) by isometric invariance.

Watrous locates the channel dilation and isometric entropy invariance. Li–Poon and Massey provide prescribed-block spectral feasibility context. The AURIC environment instrument and measured record law give the project setting for labeled physical readouts. The fixed-law fiber-flat optimization and its sharp case formulas are derived here.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Auric/CompleteRecordBudget.complete_record_budget`
- Dependency: [D5/S3/Quantum/Measurement/Auric/CompleteRecordBudgetAssembly](CompleteRecordBudgetAssembly.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/UnequalGeometry](UnequalGeometry.md)
