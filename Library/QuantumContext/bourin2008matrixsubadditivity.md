---
bibkey: bourin2008matrixsubadditivity
authors: Jean-Christophe Bourin
year: 2008
title: "Matrix subadditivity inequalities and block-matrices"
doi: 10.1142/S0129167X09005509
url: https://arxiv.org/abs/0805.1954v1
claim: "Question 1 asks whether a positive linear map reflecting positive contractions satisfies the concave functional-calculus inequality for every symmetric norm."
strata_touched:
  - D5/S3/Quantum/Schatten/BourinQuestionOneRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1142/S0129167X09005509

Source: https://arxiv.org/abs/0805.1954v1

Jean-Christophe Bourin, *Matrix subadditivity inequalities and block-matrices*, arXiv:0805.1954v1, p. 3, Question 1; published in *International Journal of Mathematics* 20 (2009), 679–691.

> Let Φ : M_n → M_k be a positive linear map between the algebras of matrices of size n and k and let F_n and F_k be the sets of non-expansive, positive operators in M_n and M_k respectively. Does Φ⁻¹(F_k) ⊂ F_n imply ‖f ∘ Φ(M)‖ ≤ ‖Φ ∘ f(M)‖ for all M ≥ 0, all symmetric norms and all non-negative concave functions on the positive half line?

Here the matrix algebras are complex. Non-expansive positive operators are the positive contractions, and symmetric norms are norms invariant under multiplication on both sides by unitary matrices. The inverse image is taken in the entire domain matrix algebra. The question uses the non-strict inclusion of sets.

The map Φ(x) = diag(x, x/4), with M = 1 and f = √, gives diagonal values (1, 1/2) and (1, 1/4); their Frobenius norm squares are 5/4 and 17/16. The corresponding Lean module proves the negative answer. No conclusion about Question 2 or the operator-norm restriction is asserted.

Literature-screen completeness is ASSUMED-UNVERIFIED. The later-paper screen recorded in issue #18573 covers arXiv:0906.1447, arXiv:1109.2384, arXiv:1012.5171 and arXiv:2307.03064; the separate Bourin questions mentioned there have different hypotheses.
