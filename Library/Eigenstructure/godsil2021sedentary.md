---
bibkey: godsil2021sedentary
authors: Chris Godsil
year: 2021
title: "Sedentary quantum walks"
doi: 10.1016/j.laa.2020.08.027
url: https://arxiv.org/abs/1710.11192v1
claim: "The paper studies continuous quantum walks U(t) = exp(itA) and their mixing matrices M(t) = U(t) ∘ conj(U(t)), shows the stay-at-home property for complete graphs, cones and several families of strongly regular graphs, and asks whether, for conference graphs, the diagonal entries of M(t) can be bounded away from zero."
strata_touched:
  - D5/S3/Quantum/Dynamics/ConferenceGraphSedentariness
license: citation-only
triage: anchor
---

# Godsil, Sedentary quantum walks

## Verified locator

DOI: https://doi.org/10.1016/j.laa.2020.08.027 (Linear Algebra and its Applications 614 (2021), 356–375).

Source: https://arxiv.org/abs/1710.11192v1

C. Godsil, arXiv:1710.11192v1 (the latest version). Quotations are from the v1 TeX source.

## Statement

For a graph $X$ with adjacency matrix $A$ the continuous quantum walk is $U(t)=\exp(itA)$, and the mixing matrix is $M(t):=U(t)\circ\overline{U(t)}=U(t)\circ U(-t)$, so $M(t)_{a,a}=|U(t)_{a,a}|^2$. For strongly regular graphs the paper computes the diagonal of the average mixing matrix, $\frac1{n^2}(1+m_\theta^2+m_\tau^2)$, derives the lower bound $n^{-2}\big(1+\tfrac12(n-1)^2\big)$, which is less than $1/2$ for $n\ge3$, so that "we get no useful information about the diagonal entries of $M(t)$", and that the bound is tight for conference graphs, the strongly regular graphs with parameters $\big(n,\tfrac{n-1}2,\tfrac{n-5}4,\tfrac{n-1}4\big)$. Section "Questions?" states:

> We do not know whether, for conference graphs, the diagonal entries of $M(t)$ can be bounded away from zero.

## Later literature

Meagher, Monterde and Nguyen ("Sedentariness in Cayley graphs", arXiv:2611.00567v1) prove that a connected integral walk-regular graph whose nonprincipal eigenvalue multiplicities share a factor $q\ge2$ is sedentary, with a non-sharp constant; this applies to conference graphs of square order $s^2$, whose two nonprincipal multiplicities $(s^2-1)/2$ are divisible by $4$, without naming them.

## Encoding and boundary

The repository writes conference graphs on $n=4m+1$ vertices with Mathlib's strongly regular predicate, the walk through the repository propagator, and $M(t)_{u,u}=|\exp(itA)_{u,u}|^2$. It proves that for every conference graph and vertex $u$ the infimum over $t>0$ of $M(t)_{u,u}$ is $1/n^2$, attained, when $n$ is a perfect square, and $0$ otherwise, and that along conference graphs of growing order no positive lower bound persists. The existence of conference graphs of a given order, other strongly regular families, Laplacian walks and average mixing are outside this conclusion.
