---
bibkey: hildebrand2007pptspectra
authors: Roland Hildebrand
year: 2007
title: "Positive partial transpose from spectra"
doi: 10.1103/PhysRevA.76.052325
url: https://arxiv.org/abs/quant-ph/0502170
claim: "For 3-by-n dimensions, absolute PPT is equivalent to two explicitly displayed 3-by-3 spectral linear matrix inequalities."
strata_touched:
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction
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
