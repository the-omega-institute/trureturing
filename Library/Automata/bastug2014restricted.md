---
bibkey: "bastug2014restricted"
authors: "Mert Baştuğ; Mihály Petreczky; Rafael Wisniewski; John Leth"
year: 2014
title: "Model Reduction of Linear Switched Systems by Restricting Discrete Dynamics"
doi: null
url: "https://arxiv.org/abs/1409.1444v2"
claim: "Regular-language reachability and unobservability spaces can be computed by finite-automaton subspace propagation with simultaneous stabilization at all automaton states."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Model Reduction of Linear Switched Systems by Restricting Discrete Dynamics

The primary text is arXiv:1409.1444v2. Section VI, Lemma 5 and
Algorithms 1–2, PDF pages 5–6, compute the span of images A_v G and the
intersection of kernels H A_v over a regular language. The algorithms
use finite-dimensional real matrices and a finite co-reachable
nondeterministic automaton with a nonempty accepting set. The empty
language is a separate zero-space case for reachability.

Algorithm 2 initializes terminal row spaces at accepting states and
propagates them backwards along transitions. Its stopping test compares
ranks at every automaton state simultaneously. A plateau at the initial
state alone is not that test. Notation 2, equation (8), uses the forward
state-word product A_ik ... A_i1; duality gives the Heisenberg effect-word
product A_i1 ... A_ik for the same chronological word.

Definition 5 and Remarks 2–3 distinguish outputs at accepted terminal
words from outputs at intermediate prefixes. These language-restricted
linear-system results are literature-attested; they do not construct
native action permissions, a physical compression or a minimal controller.
