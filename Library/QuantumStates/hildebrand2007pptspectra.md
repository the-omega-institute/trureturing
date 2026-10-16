---
bibkey: hildebrand2007pptspectra
authors: Roland Hildebrand
year: 2007
title: "Positive partial transpose from spectra"
doi: 10.1103/PhysRevA.76.052325
url: https://arxiv.org/abs/quant-ph/0502170
claim: "At fixed total dimension, APPT for a factorization with larger minimum local dimension implies APPT for one with smaller minimum local dimension; in 3-by-n dimensions APPT is equivalent to two explicit spectral LMIs."
strata_touched:
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction
  - D5/S3/Quantum/Entanglement/AbsolutePPT/FiniteBellCorner
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1103/PhysRevA.76.052325

Source: https://arxiv.org/abs/quant-ph/0502170

## Qutrit spectral criterion

Pages 5–6; the two LMIs are equation (5), and the following statement is Corollary 4. The source wording and matrices are:

Let now $m = 3$, $n \geq 3$. Then $p = 3$, $p_+ = 6$, $p_- = 3$. We shall now determine the set $\Sigma_{\pm}(3)$. If $x_1 > x_2 > x_3 > 0$, then we have
$$ x_1^2 > x_1x_2 > \max(x_2^2,x_1x_3) \geq \min(x_2^2,x_1x_3) > x_2x_3 > x_3^2.
$$
However, we can have both $x_2^2 \geq x_1x_3$ and $x_1x_3 \geq x_2^2$. Hence $\Sigma_{\pm}(3)$ consists of two
elements, and the corresponding matrices $\Lambda$ are given by
$$ \Lambda_1 = \left( \begin{array}{ccc} \lambda_{3n} & \lambda_{3n-1} & \lambda_{3n-3} \\ -\lambda_1 &
\lambda_{3n-2} & \lambda_{3n-4} \\ -\lambda_2 & -\lambda_3 & \lambda_{3n-5} \end{array} \right), \quad
\Lambda_2 = \left( \begin{array}{ccc} \lambda_{3n} & \lambda_{3n-1} & \lambda_{3n-2} \\ -\lambda_1 &
\lambda_{3n-3} & \lambda_{3n-4} \\ -\lambda_2 & -\lambda_3 & \lambda_{3n-5} \end{array} \right).
$$
Thus we obtain the two LMIs
$$
\left( \begin{array}{ccc} 2\lambda_{3n} & \lambda_{3n-1}-\lambda_1 & \lambda_{3n-3}-\lambda_2 \\ \lambda_{3n-1}-\lambda_1 &
2\lambda_{3n-2} & \lambda_{3n-4}-\lambda_3 \\ \lambda_{3n-3}-\lambda_2 & \lambda_{3n-4}-\lambda_3 &
2\lambda_{3n-5} \end{array} \right) \succeq 0, \quad \left( \begin{array}{ccc} 2\lambda_{3n} &
\lambda_{3n-1}-\lambda_1 &
\lambda_{3n-2}-\lambda_2 \\ \lambda_{3n-1}-\lambda_1 & 2\lambda_{3n-3} & \lambda_{3n-4}-\lambda_3 \\
\lambda_{3n-2}-\lambda_2 & \lambda_{3n-4}-\lambda_3 & 2\lambda_{3n-5}
\end{array} \right) \succeq 0.
$$

Corollary 4. Let $A$ be a self-adjoint PSD operator on the Hilbert space $H_{3n}$. Let $\lambda_1,\dots,\lambda_{3n}$ be the
eigenvalues of $A$ in decreasing order. Then $A$ is PPT with respect to any decomposition of $H_{3n}$ as a tensor product
$H_3 \otimes H_n$ if and only if linear matrix inequalities (5) hold.

The delivery uses the necessary direction only. The Lean nine-coordinate boundary vector contains the top three eigenvalues followed by the bottom six, all in decreasing order; source indices start at one and Lean Fin indices start at zero.


## Fixed-total-dimension monotonicity

Theorem 2, PDF page 5, states: let $N=n_1m_1=n_2m_2$ with
$p_1=\min(n_1,m_1)\geq p_2=\min(n_2,m_2)$. A self-adjoint positive
semidefinite operator on $H_N$ that is PPT with respect to every
decomposition $H_N=H_{n_1}\otimes H_{m_1}$ is also PPT with respect to
every decomposition $H_N=H_{n_2}\otimes H_{m_2}$.

Thus APPT for $4\times6$ implies APPT for $3\times8$, since both total
dimensions are 24 and $4\geq3$. The tensor identification is unitary;
trace and purity are unchanged. Combining this implication with the
established qutrit dimension-24 maximum $32/26^2=8/169$ gives the same
upper bound for $4\times6$. The known ray $(I+2|\psi\rangle\langle\psi|)/26$
is APPT in $4\times6$ and attains the bound. This scalar application is
therefore a consequence of existing mathematics, not an independent
open-problem resolution. The generic product Bell-corner construction is
a direct formal route to the necessary LMIs; it does not assume that
arbitrary global coordinate packings commute with partial transpose.

Theorem 2 preserves total dimension. It gives no transfer from dimension
20 to dimensions 18 or 21, no result for dimension 28 by the
$3\times8$ bound, no classification of maximizers, and no equivalence
between APPT and absolute separability.
