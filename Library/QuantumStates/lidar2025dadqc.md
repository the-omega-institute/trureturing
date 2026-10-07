---
bibkey: lidar2025dadqc
authors: D. A. Lidar
year: 2025
title: "Digital-Analog-Digital Quantum Supremacy"
doi: 10.48550/arXiv.2512.07127
url: https://arxiv.org/abs/2512.07127v1
claim: "Let $\\{\\mH_n\\}$ be a family of hardware graphs as in \\cref{def:QPU-R-E}. For each $n$, draw $\\mG\\sim \\mathrm{Unif}[\\mF_d(\\mH_n)]$ and $\\theta\\sim \\mathrm{Unif}[0,2\\pi)^n$. For any fixed choice of single-qubit angles $\\{v_i\\}$ in \\cref{eq:HZ'}, there exist constants $a,b>0$ (depending only on $d$) such that for every $s\\in\\{0,1\\}^n$, $\\Pr_{\\mG,\\theta} \\bigl[ P_{\\UIQP^{(\\theta)}}(s)\\ge a 2^{-n} \\bigr] \\ge b.$"
strata_touched:
  - D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation
license: citation-only
triage: anchor
---

# Digital-Analog-Digital Quantum Supremacy

D. A. Lidar's paper studies QPU-restricted IQP circuits and states an anticoncentration conjecture for every fixed hardware-graph family and fixed one-qubit angles.

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2512.07127

Source: https://arxiv.org/abs/2512.07127v1

Definition 1 (p. 4), verbatim from the source TeX:

> Let $\mH_n=(\mV_{\mH},\mE_{\mH})$ be a fixed simple $D$-regular hardware graph on $n$ labeled vertices, and let $3\le d\le D$ be a fixed constant ($n$-independent). The \emph{$d$-factors} of a graph $\mH$ are \mF_d(\mH) \equiv \{\mG=(\mV,\mE_{\mG}) : \mE_{\mG}\subseteq \mE_{\mH},\deg_{\mG}(v)=d\ \forall v\in\mV\}. The \emph{QPU-restricted graph ensemble} is the probability space $\mathrm{Unif}[\mF_d(\mH_n)]$ in which, for each run of $\UDAD$, a graph $\mG\in\mF_d(\mH_n)$ is drawn uniformly at random.

Eqs. (17)–(20) specify the factor set, random-angle layer, circuit with its Hamiltonian, and anticoncentration event. Conjecture 2 (p. 4, labelled `conj:host-anticonc`) reads:

> Let $\{\mH_n\}$ be a family of hardware graphs as in \cref{def:QPU-R-E}. For each $n$, draw $\mG\sim \mathrm{Unif}[\mF_d(\mH_n)]$ and $\theta\sim \mathrm{Unif}[0,2\pi)^n$. For any fixed choice of single-qubit angles $\{v_i\}$ in \cref{eq:HZ'}, there exist constants $a,b>0$ (depending only on $d$) such that for every $s\in\{0,1\}^n$, $\Pr_{\mG,\theta} \bigl[ P_{\UIQP^{(\theta)}}(s)\ge a 2^{-n} \bigr] \ge b.$

The source's Theorem 2 assumes Conjecture 2. The Lean settlement uses the fixed choice $v_i=\pi/7$, the cyclic twin-pair hardware family with $n=6m$, and proves the negation of the conjecture's conclusion.
