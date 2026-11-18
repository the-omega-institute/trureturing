---
bibkey: hameed2025signedspectraldeletion
authors: Shahul Hameed K, Biju K and Zoran Stanić
year: 2025
title: Spectral measures of balance for signed graphs
doi: null
url: https://ajc.maths.uq.edu.au/v93.p198
claim: "Equation (1) defines beta_A as the squared distance between the ordered signed and underlying adjacency spectra; MathOverflow 479815 asks its deletion monotonicity."
strata_touched:
  - D5/S3/Combinatorics/SignedGraphSpectral/MO479815
license: citation-only
triage: anchor
---

# Spectral measures of balance for signed graphs

## Verified locator

- DOI: null
- URL: https://ajc.maths.uq.edu.au/v93.p198

The publisher identifies the paper's license as CC BY 4.0. This note retains a citation and the mathematical definition, without copying the paper's exposition.

MathOverflow question 479815, revision 2, “Change in two spectral deviations due to edge deletion in a signed graph”:
https://mathoverflow.net/questions/479815

The cited source paper is Shahul Hameed K, Biju K and Zoran Stanić, *Spectral measures of balance for signed graphs*, Australasian Journal of Combinatorics 93(1) (2025), 198–210, equation (1):
https://ajc.maths.uq.edu.au/download/93/ajc_v93_p198.pdf

The source defines

$$
\beta_A(\Sigma)=\sum_i(\lambda_i-\mu_i)^2,
$$

where $(\lambda_i)$ and $(\mu_i)$ are the full nonincreasing real adjacency spectra, with multiplicity, of the signed graph and its underlying graph. The MathOverflow question asks whether, for every finite graph, every legal signing, and every edge $e$,

$$
\beta_A(\Sigma-e)\leq \beta_A(\Sigma).
$$

Deletion keeps the vertex set and changes the underlying graph as well as the signed graph. The source and its comments impose no connectedness, non-isolation, non-bridge, dimension, or sign restriction for this beta claim.

## Formal correspondence

`D5/S3/Combinatorics/SignedGraphSpectral/MO479815.lean` represents every finite carrier by `Fin n`, every unordered-pair signing by `Sym2 (Fin n) → Bool`, and uses the actual `SimpleGraph.deleteEdges` operation on the same carrier. `orderedSpectrum` is the full decreasing Hermitian spectrum indexed by `Fin n`, and `beta` is the source sum of squared coordinate differences. The public declarations are the literal `claim : Prop` and `result : ¬ claim`.

## Refuting witness

Use the paw graph on vertices $0,1,2,3$ with edges $01,02,12,03$, give all edges the negative sign, and delete the pendant edge $03$. Its underlying adjacency matrix is

$$
A=\begin{pmatrix}0&1&1&1\\1&0&1&0\\1&1&0&0\\1&0&0&0\end{pmatrix},
$$

and after deletion it is $K_3\sqcup K_1$ with matrix

$$
B=\begin{pmatrix}0&1&1&0\\1&0&1&0\\1&1&0&0\\0&0&0&0\end{pmatrix}.
$$

The characteristic polynomial of $A$ is $(t+1)(t^3-t^2-3t+1)$. The cubic has one root $a\in(2,3)$, one root $b\in(0,1)$, and one root $c\in(-2,-1)$, with $a+b+c=1$. The ordered spectra are

$$
\operatorname{spec}(A)=(a,b,-1,c),\quad
\operatorname{spec}(-A)=(-c,1,-b,-a),
$$

and after deletion

$$
\operatorname{spec}(B)=(2,0,-1,-1),\quad
\operatorname{spec}(-B)=(1,1,0,-2).
$$

Consequently $\beta_A(\Sigma)=4(1-b)^2$ before deletion and $\beta_A(\Sigma-e)=4$ after deletion. Since $0<b<1$, the latter is strictly larger.

## Literature boundary

The bounded screen included the named MathOverflow source, the cited paper, and the directly relevant follow-up records arXiv:2606.11108 and the full HTML record for arXiv:2609.11736. No complete supplier of this exact universal claim or this proof was found in that scope. This is a bounded literature statement, not an exhaustive priority claim.

## Repository status

The result is an external open-problem refutation. The Lean proof is closed over the standard Mathlib axiom closure; freeze, coverage, independent pre-freeze review, required CI, and merge remain separate delivery obligations.
