---
bibkey: quesne2023keplercoulomb
authors: C. Quesne
year: 2023
title: "Quasi-exactly solvable extensions of the Kepler-Coulomb potential on the sphere"
doi: 10.1016/j.aop.2023.169265
url: https://arxiv.org/abs/2206.01033v3
claim: "For the generating-function construction of quasi-exactly solvable extensions of the Kepler-Coulomb potential on the sphere, the m + 1 coefficients a_0, …, a_m solve the linear system (4.13)–(4.17). The author conjectures that for every m > 1 the solution has the closed forms (4.19)–(4.24), with a common denominator Q^{2µ} + b_1κQ^{2µ−2} + ⋯ + b_µκ^µ and positive constants b_j and c_j^{(k)}. The conjecture is confirmed for m ≤ 7, and proving it by finding the constants is stated as open."
strata_touched:
  - D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients
license: citation-only
triage: anchor
---

# Quesne, quasi-exactly solvable extensions of the Kepler–Coulomb potential on the sphere

C. Quesne, *Quasi-exactly solvable extensions of the Kepler-Coulomb potential on the sphere*, Ann. Phys. **451**, 169265 (2023), DOI 10.1016/j.aop.2023.169265; arXiv:2206.01033 [math-ph] (v3, the latest of versions v1–v3).

## Verified locator

DOI: 10.1016/j.aop.2023.169265 (as listed on the arXiv abstract page).
Primary version read: https://arxiv.org/abs/2206.01033v3.
Source: https://arxiv.org/pdf/2206.01033v3 (text read from the PDF):
- §4.1, (4.10)–(4.11), the ansatz for W₊ with the m + 1 constants a_0, …, a_m and the values for m = 1, 2, 3;
- §4.2, (4.12)–(4.18), the linear system;
- §4.2, the Conjecture, (4.19)–(4.24);
- §5, the statement that the conjecture remains to be proved.

## Source statements

§4.2: "On equating their coefficients, we get the relations
(m + 1)a_0 − a_1 = 1, (4.13)
mQa_0 − Qa_1 − Σ_{k=1}^{[m/2]} a_{2k} = 0, (4.14)
(m − 2k)a_{2k} − Qa_{2k+1} − Σ_{l=k+1}^{[m/2]} a_{2l} = 0, k = 1, 2, …, [(m − 1)/2], (4.15)
κ(m + 1 − 2k)a_{2k−1} − Qa_{2k} − κ(m + 1 − 2k)a_{2k+1} = 0, k = 1, 2, …, [m/2] − 1, (4.16)
½(1 − (−1)^m)(2κa_{m−2} − Qa_{m−1} − 2κa_m) + ½(1 + (−1)^m)(κa_{m−1} − Qa_m) = 0, (4.17)
Q − Qa_0 − Σ_{k=1}^{[m/2]} a_{2k} = 0, (4.18)
which form a system of m + 1 linear equations in the m + 1 unknowns a_0, a_1, …, a_m because the last equation (4.18) turns out to be a combination of Eqs. (4.13) and (4.14)."

§4.2: "Conjecture For any m > 1, the solution of the system of equations (4.13)–(4.17) can be written as …" For m = 2µ + 1, (4.19)–(4.21):

$$
a_0=\frac{(Q^2+4\kappa)(Q^2+16\kappa)\cdots(Q^2+4\mu^2\kappa)}{\Delta},\qquad
a_{2k}=\frac{(2\mu+1)!}{(2\mu-2k+1)!}\,\frac{\kappa^kQ(Q^2+4\kappa)\cdots(Q^2+4(\mu-k)^2\kappa)}{\Delta},
$$

$$
a_{2k+1}=\frac{(2\mu+1)!}{(2\mu-2k)!}\,\frac{\kappa^k\bigl(Q^{2\mu-2k}+c^{(k)}_1\kappa Q^{2\mu-2k-2}+\cdots+c^{(k)}_{\mu-k}\kappa^{\mu-k}\bigr)}{\Delta}.
$$

For m = 2µ, (4.22)–(4.24):

$$
a_0=\frac{(Q^2+\kappa)(Q^2+9\kappa)\cdots(Q^2+(2\mu-1)^2\kappa)}{\Delta},\qquad
a_{2k}=\frac{(2\mu)!}{(2\mu-2k)!}\,\frac{\kappa^kQ(Q^2+\kappa)\cdots(Q^2+(2\mu-2k-1)^2\kappa)}{\Delta},
$$

$$
a_{2k+1}=\frac{(2\mu)!}{(2\mu-2k-1)!}\,\frac{\kappa^kQ^2\bigl(Q^{2\mu-2k-2}+c^{(k)}_1\kappa Q^{2\mu-2k-4}+\cdots+c^{(k)}_{\mu-k-1}\kappa^{\mu-k-1}\bigr)}{\Delta}.
$$

Here Δ = Q^{2µ} + b_1κQ^{2µ−2} + b_2κ²Q^{2µ−4} + ⋯ + b_µκ^µ, "where b_1, b_2, …, b_µ, and c^{(k)}_1, c^{(k)}_2, …, c^{(k)}_{µ−k} or c^{(k)}_{µ−k−1} are some positive constants."

§5: "All the aspects of this conjecture and the consequences drawn from it for the first two eigenstates of V(r) have been confirmed for m ≤ 7. The problem that remains open is to prove our conjecture by finding the explicit values of the constants appearing …"

## Reading used by the repository

Q and κ are positive. In (4.13)–(4.24), Q is the rescaled coupling Q/[2(L + 1)(L + 2)] introduced in §3, where the Coulomb coupling Q is positive (Eq. (2.26)). κ is the curvature of the sphere, with r ∈ (0, 1/√κ). The unknowns a_0, …, a_m are read as a function of the index on 0, …, m. The conjecture is read as: for every m ≥ 2 there are positive constants b_j and c_j^{(k)}, independent of Q and κ, such that for all Q, κ > 0 the system (4.13)–(4.17) has a solution, every solution has the closed forms above, and any two solutions agree on 0, …, m. Equation (4.18) is not part of the system, as the source states.
