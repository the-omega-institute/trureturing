---
bibkey: peledteenicarmicohen2021minor
authors: Bar Y. Peled; Amit Te'eni; Avishy Carmi; Eliahu Cohen
year: 2021
title: "Correlation minor norms, entanglement detection and discord"
doi: 10.1038/s41598-021-82303-3
url: "https://arxiv.org/abs/2005.12079v2"
claim: "The paper defines the correlation minor norms of a bipartite state as Schatten norms of compound matrices of its correlation matrix, bounds them for separable states in filter normal form, constructs saturating states from quantum designs, and conjectures that the bounds hold without the filter-normal-form assumption."
strata_touched:
  - D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation
  - D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormGeometry
  - D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormDesignObstruction
  - D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormTetrahedron
  - D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormQubitBound
  - D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormSpectral
  - D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance
  - D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior
  - D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCCNR
license: citation-only
triage: anchor
---

# Peled, Te'eni, Carmi and Cohen, Correlation minor norms, entanglement detection and discord

B. Y. Peled, A. Te'eni, A. Carmi and E. Cohen, Scientific Reports 11 (2021) 2849, DOI 10.1038/s41598-021-82303-3; arXiv:2005.12079v2. Quotations are from the arXiv v2 TeX source.

For orthonormal bases $\{A_i\}$, $\{B_j\}$ of the Hermitian matrices on $\mathbb C^{d_A}$ and $\mathbb C^{d_B}$, the correlation matrix of a state $\rho$ is $\mathcal C_{ij}=\operatorname{tr}(\rho\,A_i\otimes B_j)$, and $\mathcal M_{h,p}$ is the Schatten $p$-norm of its $h$-th compound matrix. With $d=\min(d_A,d_B)$ and $D=\max(d_A,d_B)$, Theorem 3 states: "Let $ \rho $ be a separable state in FNF, and $h \geq \sqrt{Dd}$. Then: $\mathcal{M}_{h,p=\infty} \leq \frac{1}{\sqrt{Dd}} \left[ \frac{D-1}{D \left(h-1\right)} \frac{d-1}{d \left(h-1\right)} \right]^{\frac{h-1}{2}}$." The paper adds:

> As in Theorem \ref{thm_bound_p_1}, we conjecture this theorem still holds without the assumption that $\rho$ is in FNF.

## Verified locator

Source: https://arxiv.org/abs/2005.12079v2
- DOI: https://doi.org/10.1038/s41598-021-82303-3 (journal version; title, authors, journal, volume, issue and article number from Crossref; the journal text was not read).
- URL: https://arxiv.org/abs/2005.12079v2. The e-print member `CMN_16_12_20_arXiv.tex` has 378 lines and md5 `8c626d38169cc53f41f01da6643e7760`. Locations:
  - the correlation matrix, l. 177–183;
  - the correlation minor norms and the compound matrix, l. 214–233;
  - filter normal form, l. 248; Theorem 3 and the conjecture, l. 274–281.


## Complete-family formal-return attribution and scope

The received note is by Haobo Ma (Chrono AI, Singapore) and Wenlin Zhang (National University of Singapore and Chrono AI, Singapore), copyright 2026, CC BY 4.0. Its cited works and existing formal suppliers retain their own licenses. The source note and scientific planning conclusions are disclosed fallible dependencies; neither supplies independent final review, novelty endorsement, authorship consent or permission for correspondence, publication or submission. The original intake disclosed communication-framing exposure and the inherited repository context is prior-exposed. No context-sterility claim is made.

The covariance estimate is prior work of C.-J. Zhang, Y.-S. Zhang, S. Zhang and G.-C. Guo, *Entanglement detection beyond the computable cross-norm or realignment criterion*, Physical Review A 77, 060301(R) (2008), Theorem 1, DOI [10.1103/PhysRevA.77.060301](https://doi.org/10.1103/PhysRevA.77.060301), arXiv:0709.3766v6; and O. Gittsovich, O. Gühne, P. Hyllus and J. Eisert, *Unifying several separability conditions using the covariance matrix criterion*, Physical Review A 78, 052319 (2008), Proposition IV.2, DOI [10.1103/PhysRevA.78.052319](https://doi.org/10.1103/PhysRevA.78.052319), arXiv:0803.0757v3. The formal tail bound is its normalized application and the correction of printed D31, not a new covariance theorem.

C.-K. Li, Y.-T. Poon and N.-S. Sze, *A note on the realignment criterion*, Journal of Physics A: Mathematical and Theoretical 44, 315304 (2011), DOI [10.1088/1751-8113/44/31/315304](https://doi.org/10.1088/1751-8113/44/31/315304), arXiv:1103.2499v2, already give the normalized-identity singular-value observation in Lemma 2.1 and the equal-dimensional p=1 comparison in Theorem 2.4. These bibliographic and locator details are inherited from the size/hash-bound received scientific note, not a fresh reading of those articles.

The formal return retains Peled Theorem 1's separability/FNF, D<=d cubed and h>1 hypotheses and Theorem 3's separability/FNF and sqrt(Dd)<=h<=d squared hypotheses. Only their conjectured removal of FNF is refuted. Theorems 2 and 4 assume existing common-size pairs of regular coherent degree-one pure designs; they do not prove existence in all dimensions/cardinalities. The precise coherent-pair obstruction does not refute all interpretations of the broad general-p design suggestion. The corrected square-root tail does not validate Appendix D.5's numerical simultaneous-saturation and active-constraint assumptions.

The universal qubit fourth-order upper bound is sharp for every D>=4; no sharpness at D=2,3 or classification of all maximizers is claimed. The CCNR specialization covers d<=h<=d squared at equal dimensions for the operator norm, and every Schatten p at full order; intermediate finite p, h<d and unequal/general dimensions remain open here. Other orders/dimensions, arbitrary design interpretations, operator-Schmidt/entropy context, the reported CMN-versus-CCNR numerical example and discord/Theorem 5 remain outside the note's claimed new coverage. The received source reading of Sections I-VI, Appendices A-E and references of arXiv v2 is a supplier report; the earlier journal-text access limitation remains.
