---
bibkey: ferenczizamboni2024arnouxrauzy
authors: Sebastien Ferenczi; Luca Q. Zamboni
year: 2024
title: "Clustering and Arnoux-Rauzy words"
doi: 10.1016/j.aam.2023.102621
url: https://arxiv.org/abs/2305.18986v1
claim: "Section 2 defines the Burrows–Wheeler transform and perfect clustering; Section 4.1 defines Arnoux–Rauzy languages and standard words; Proposition 14 constructs a primitive perfectly clustering word conjugate to a standard Arnoux–Rauzy word; Conjecture 1 asserts that it is the longest clustering word or the longest such conjugate."
strata_touched:
  - D5/S1/Words/ArnouxRauzyLongestClusteringRefutation
license: citation-only
triage: anchor
---

# Clustering and Arnoux–Rauzy words

Ferenczi and Zamboni study the Burrows–Wheeler transform $B(w)$, the last
column of the lexicographically sorted conjugates of a word. They call $w$
*clustering for the permutation* $\pi$ when the transform is a concatenation
of constant blocks $(\pi a_1)^{n_{\pi a_1}}\cdots(\pi a_r)^{n_{\pi a_r}}$;
perfect clustering means clustering for the symmetric permutation.

An Arnoux–Rauzy language starts with $A_0=a$, $B_0=b$, $C_0=c$ and repeatedly
uses one of the three rules. For example, rule $(a)$ fixes $A_k$ and appends
$A_k$ to both $B_k$ and $C_k$. Each rule occurs infinitely often. Factors of
the resulting blocks form the language, and an $A_k$, $B_k$, or $C_k$ is a
standard Arnoux–Rauzy word.

The condition $(Rabc)$ says that the rule at stage $0$ is $(a)$ and that the
first rule different from $(a)$ is $(b)$. Proposition 14 states: “The word
$v=S_{\mu_y}^{\mu_y-\mu+1}M_{\mu_y}$ is a primitive perfectly clustering [...]
word of $\Lambda$ conjugate to a standard AR word.” Conjecture 1 then asks:
“In a given AR language $\Lambda$ satisfying $(Rabc)$, the word in Proposition
[14] is the longest clustering word, or, if this fails, the longest clustering
word conjugate to a standard AR word.”

## Verified locator

DOI: https://doi.org/10.1016/j.aam.2023.102621

Source: https://arxiv.org/abs/2305.18986v1
