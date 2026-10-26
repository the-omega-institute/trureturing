---
bibkey: watrous2011quantumcircuits
authors: John Watrous
year: 2011
title: An introduction to quantum information and quantum circuits
doi: null
url: https://cs.uwaterloo.ca/~watrous/Papers/IntroductionQuantumCircuits.pdf
claim: BQP uses polynomial-time uniform quantum circuits with bounded error on every input.
strata_touched: []
license: citation-only
triage: anchor
---

# Uniform circuits and reliable answers

The author-hosted version is dated June 22, 2011. Section 4.1,
Definition 3 (PDF p. 12), defines BQP by a polynomial-time uniform circuit
family whose single output bit is correct with probability at least
$2/3$ on both positive and negative inputs. Section 4.2 explains
independent repetition and the classical control used in circuit
composition. Uniformity includes producing the finite circuit
descriptions; an input-dependent uncharged preparation or control oracle
is not supplied by the definition.

For a polynomial-time verifier $V$ and $m$ witness bits, the unitary
verification experiment starting from a uniform witness register has
success probability

$$
2^{-m}\#\{w:V(x,w)=1\}.
$$

This follows by summing the squared amplitudes of the orthogonal
successful basis branches. A unique successful witness therefore gives
probability $2^{-m}$ in this particular experiment. The normalized
conditional success state does not supply its own high-probability
preparation procedure. This observation is not a lower bound for every
algorithm using the instance's structure.

A uniform polynomial quantum circuit solver for all SAT instances would
give $\mathrm{NP}\subseteq\mathrm{BQP}$ by the classical NP reductions.
Classical $\mathrm P=\mathrm{NP}$ additionally needs a deterministic
polynomial classical decision algorithm; quantum gate counting alone
does not provide it. No external physical clock is required for either
circuit-complexity definition.
