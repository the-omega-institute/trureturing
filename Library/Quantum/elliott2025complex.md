---
bibkey: elliott2025complex
title: Strict advantage of complex quantum theory in a communication task
authors: Thomas J. Elliott
year: 2025
url: https://arxiv.org/abs/2505.16523v2
claim: A four-input communication task admits a complex-qubit strategy but no real-qubit strategy; non-real Bargmann invariants witness the ensemble's basis-independent imaginarity. Appendix D shows that a rebit strategy reaches average trace distance d = 1/12 from the target distribution and weakly conjectures that 1/12 is the minimum.
strata_touched:
  - D5/S3/QuantumBounds/RebitExclusionDistance
license: citation-only
triage: anchor
doi: 10.1103/PhysRevA.111.062401
---

# Complex dimension advantage and relational witnesses

Elliott, arXiv:2505.16523v2 (version dated 2 June 2025; manuscript dated
11 June 2025), studies the target conditional distribution
$P(y\mid x)=(1-\delta_{xy})/3$ on four symbols. Section III proves that
complex quantum theory attains communication cost $D=1$, corresponding
to a qubit, while classical and real quantum strategies require a larger
cost under the paper's task assumptions. This is an existing operational
separation between real and complex quantum state spaces.

Section II.B, equation (2), and Appendix B define Bargmann invariants as
traces of products of density matrices. Their invariance under a common
unitary and the reality of products of real matrices imply that a
non-real invariant rules out one basis in which the entire ensemble is
real. First- and second-order invariants are always real; third or higher
order is needed for this witness. Section III.E, equation (6), finds
$B_{0,1,2}=\mp i/(3\sqrt3)$ for the task's optimal strategies.

The communication task does not impose a continuum of programmable Schur
channels, prescribed Fisher-information equality and optimal curvature,
or one analytic preparation curve through specified nodes. The quantum
volume's program-support dimension question requires those additional
constraints and its own rigidity and continuation proof. A strict
real/complex dimension difference, or the use of an imaginary Bargmann
invariant by itself, should not be presented as a new general principle.

The paper attributes relational-state measurements to Oszmaniec, Brod
and Galvão, *Measuring relational information between quantum states,
and applications*, New Journal of Physics **26**, 013053 (2024), and set
imaginarity witnesses to Fernandes et al., arXiv:2403.15066. These pointers
do not substitute for inspecting the source when using a stronger
realification or measurement theorem.

## Verified locator

DOI: 10.1103/PhysRevA.111.062401 (Phys. Rev. A 111, 062401, from Crossref metadata; the journal full text was not read).
Primary version read: https://arxiv.org/abs/2505.16523v2 (the latest arXiv version).
Source: https://arxiv.org/pdf/2505.16523v2 (text read from the PDF):
- §II and §III.A, the task;
- §IV, the robustness question;
- Appendix D, "Bounding the distance for rebit strategies".

## The rebit distance

§III.A: "X = Y = {0, 1, 2, 3} … The target distribution for the game is P(Y|X) = (1 − δ_XY)/3".

§IV: "For the trace distance, this would be d = (1/|X|) Σ_{x∈X} (1/2) Σ_{y∈Y} |P(y|x) − P̃(y|x)|, where P and P̃ are the target and realised distributions respectively. … Through an explicit construction we show that d = 1/12 is achievable for a rebit strategy. … Based on a rudimentary attempt at optimisation, we weakly conjecture that this is the optimal rebit strategy according to the average trace distance".

Appendix D: "Through a rudimentary search over rebit strategies with gradient descent and Bayesian optimisation approaches, we were unable to find a rebit strategy with smaller error than this. … We therefore only weakly conjecture that d = 1/12 the the minimum distance for a rebit strategy."

This note paraphrases the cited result and scope. No article PDF, figure
or extended excerpt is redistributed.
