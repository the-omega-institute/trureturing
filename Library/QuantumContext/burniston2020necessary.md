---
bibkey: burniston2020necessary
authors: John Burniston; Michael Grabowecky; Carlo Maria Scandolo; Giulio Chiribella; Gilad Gour
year: 2020
title: "Necessary and sufficient conditions on measurements of quantum channels"
doi: 10.1098/rspa.2019.0832
url: https://arxiv.org/abs/1904.09161v5
claim: "In finite dimensions, a CPP, CPTNI-preserving supermap is completable to a superchannel exactly when it is completely CPTNI-preserving; a jointly normalized super-instrument has a common CPTP preprocessor and a CPTNI postprocessing instrument."
strata_touched: []
license: citation-only
triage: anchor
---

# Probabilistic channel transformations and their common normalization

The source is arXiv:1904.09161v5, published in *Proceedings of the Royal
Society A* 476, 20190832. The definitions and results below use the v5
numbering. They are literature results, with the stated specializations;
no new theorem, priority or Lean verification is claimed.

## Finite-dimensional hypotheses and completion

Write $A=(A_0,A_1)$, with $A_0$ the input and $A_1$ the output of
the inserted map, and similarly $B=(B_0,B_1)$. All Hilbert spaces are
finite-dimensional. A supermap $\Theta^{A\to B}$ is a linear map from
linear maps $A_0\to A_1$ to linear maps $B_0\to B_1$.

- **CPP** means completely CP-preserving: for every ancillary pair
  $R=(R_0,R_1)$ and every bipartite CP map $\mathcal E^{RA}$,
  $(\mathrm{id}^R\otimes\Theta)[\mathcal E^{RA}]$ is CP
  (§2, Eq. (2.1)).
- **CPTNI-preserving** means CPP and
  $\operatorname{Tr}\Theta[\mathcal N](\rho)\leq1$ for every CPTP
  $\mathcal N^{A_0\to A_1}$ and every density matrix $\rho^{B_0}$
  (§2, Eq. (2.2)). For CPP supermaps, testing CPTP inserted maps is
  equivalent to sending every CPTNI inserted map to a CPTNI map
  (Appendix A).
- **Completely CPTNI-preserving** additionally requires

  $$
  \operatorname{Tr}(\mathrm{id}^R\otimes\Theta)
       [\mathcal N^{RA}](\rho^{R_0B_0})\leq1
  $$

  for every ancillary pair $R$, bipartite CPTP map $\mathcal N^{RA}$
  and density matrix $\rho^{R_0B_0}$ (§3, Eq. (3.1)). The inserted
  channel and the test input may have joint correlations.

Theorem 4.1, proved as Theorem D.1 in Appendix D, states that a
CPTNI-preserving $\Theta$ admits another CPTNI-preserving
$\Theta_{\mathrm f}$ with $\Theta+\Theta_{\mathrm f}$ a superchannel
if and only if $\Theta$ is completely CPTNI-preserving. A superchannel
is a CPP supermap taking CPTP maps to CPTP maps; Appendix A explains why
this deterministic condition already holds completely.

For a finite collection of CPP branches $\{\Theta_x\}$, apply the
completion criterion to the aggregate
$\Theta_{\mathrm S}=\sum_x\Theta_x$. If this aggregate is completely
CPTNI-preserving, a complementary failure branch completes the
collection to one super-instrument. Conversely, a subcollection of an
actual super-instrument has a completely CPTNI-preserving aggregate.
Separate completability of each branch does not establish joint
normalization: for example, two copies of a superchannel are each
completable but their sum has trace two on normalized tests.

For an **already jointly normalized** finite family
$\sum_x\Theta_x=\Phi$, with $\Phi$ a superchannel, §5, Eq. (5.1),
and Proposition E.1 give a finite memory $E$ and

$$
\Theta_x[\mathcal N]
 =\Gamma_{\mathrm{post},x}\circ
   (\mathcal N\otimes\mathrm{id}_E)\circ\Gamma_{\mathrm{pre}},
$$

where $\Gamma_{\mathrm{pre}}:B_0\to A_0E$ is CPTP, each
$\Gamma_{\mathrm{post},x}:A_1E\to B_1$ is CPTNI, and
$\sum_x\Gamma_{\mathrm{post},x}$ is CPTP. The same preprocessor
works for every outcome of this one instrument, including its
completion branch. The formula does not identify separately chosen
preprocessors of unrelated branches.

## Ordinary preservation is insufficient

Appendix B.1 uses the unnormalized, input-first Choi operator

$$
J_{\mathcal N}=(\mathrm{id}_{A_0}\otimes\mathcal N)
       (|\Omega\rangle\langle\Omega|),\qquad
|\Omega\rangle=\sum_a|a,a\rangle.
$$

Thus $\mathcal N$ is CPTP exactly when
$J_{\mathcal N}\succeq0$ and
$\operatorname{Tr}_{A_1}J_{\mathcal N}=I_{A_0}$;
its trace is $\dim A_0$, not one. For a supermap Choi operator
$J_\Theta^{AB}$, CPP is $J_\Theta\succeq0$. Put
$Q=\operatorname{Tr}_{B_1}J_\Theta$. Equations (4.1)–(4.2) compare

$$
\begin{aligned}
\operatorname{Tr}[Q(J_{\mathcal N}\otimes\rho^{B_0})^{\mathsf T}]
  &\leq1,\\
\operatorname{Tr}[Q M^{\mathsf T}]&\leq1
 \quad\text{for every }M\succeq0,\quad
 \operatorname{Tr}_{A_1}M=I_{A_0}\otimes\rho^{B_0}.
\end{aligned}
$$

The first is ordinary CPTNI preservation; the second is complete
CPTNI preservation. In these tests $\mathcal N$ ranges over CPTP maps
and $\rho^{B_0}$ over density matrices. Every transpose here is the full
matrix transpose in the fixed product basis.

In Eq. (2.4) and Appendix C all four systems are qubits. The example has

$$
J_\Theta=I_{A_0}\otimes|\psi^-\rangle\langle\psi^-|_{A_1B_0}
                 \otimes I_{B_1}/2,\qquad
|\psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2.
$$

It is positive and passes every product test in the first inequality.
Taking $M=Q^{\mathsf T}$ gives the allowed marginal
$I_{A_0}\otimes I_{B_0}/2$, but
$\operatorname{Tr}(QM^{\mathsf T})=2>1$.
Hence it cannot be a branch of a physical channel super-instrument,
despite being CPP and ordinarily CPTNI-preserving.

This distinction concerns transformations **of maps**. For an ordinary
state instrument, CP branches $\mathcal E_x$ are jointly normalized
when $\sum_x\mathcal E_x$ is CPTP. A CP trace-nonincreasing state map
can be completed to such an instrument; it is not subject to an
additional independent higher-order preservation test.

## Scalar outputs, grouped slots and original success

With $B_0=B_1=\mathbb C$, Appendix B.1, Eq. (B.2), gives

$$
p_x(\mathcal N)=\operatorname{Tr}(J_{\Theta_x}J_{\mathcal N}^{\mathsf T})
              =\operatorname{Tr}(T_xJ_{\mathcal N}),\qquad
T_x=J_{\Theta_x}^{\mathsf T}\succeq0.
$$

For a normalized one-slot instrument the shared preparation has an
input marginal $\sigma$, and
$\sum_xT_x=\sigma^{\mathsf T}\otimes I_{A_1}$.
This is tester normalization, not the usual POVM normalization on
the Choi space. It allows an arbitrary finite probe memory; it does
not assume supplied normalized Choi states.

A parallel group of $N$ memoryless channel uses may be treated as
one inserted channel $\mathcal N^{\otimes N}$ on the grouped input
and output spaces. After a fixed tensor permutation, its Choi operator
is $J_{\mathcal N}^{\otimes N}$, so the same pairing applies. This
grouped-slot statement supplies no interleaved adaptive $N$-slot
realization. The fixed-order adaptive application is given separately
in the [amplitude-damping problem dossier](../../Problems/sekatski-guryanova-kothakonda-skotiniotis-2025-amplitude-damping-measure-prepare-cloning.md),
using the [existing quantum-network source](../QuantumChannels/chiribella2009networks.md).

The native state-conversion contract in
[VIII, §§248–250](../../docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VIII.md)
supplies same-source states, not callable unknown channels. Its finite
success branches are ordinary state maps. If the erased success map is
$\mathcal E=\sum_{h\in\mathrm S}\mathcal E_h$, then

$$
s_{\mathcal E}(q)=\operatorname{Tr}\mathcal E(\rho_q^{\otimes k}),
\qquad
\rho_{\mathrm{out},q}
 =\frac{\mathcal E(\rho_q^{\otimes k})}{s_{\mathcal E}(q)},
\qquad
\Pr(\text{original success})=P_q^k s_{\mathcal E}(q).
$$

The normalized expression is defined only for positive success. For an
already allowed native map, an independent fixed coin retaining a
fraction $c\in(0,1]$ multiplies the original success by $c$ and
preserves this conditional output. Branch-dependent scaling can change
the erased mixture; division by source-dependent success is
conditioning, not a physical installation.

Neither the supermap completion theorem nor a state-map completion
provides number-preserving LOCC realization, a preparation-to-channel
conversion, an auxiliary resource or a polynomial original yield.
The [five-mode decoder, §§15–16](../../docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md)
returns a classical state description modulo one common conjugation;
it is not a channel-query, preparation or continuation interface.
The simultaneous native approximation and yield assertion (248.4)
remains unresolved.

## Locator

- DOI: https://doi.org/10.1098/rspa.2019.0832
- Versioned source: https://arxiv.org/abs/1904.09161v5
- Original PDF: https://arxiv.org/pdf/1904.09161v5
- Definitions: §2, Eqs. (2.1)–(2.3), PDF p. 2; §3, Eq. (3.1), p. 3.
- Completion: §4, Theorem 4.1, pp. 3–4; Appendix D, Theorem D.1.
- Realization: §5, Eq. (5.1), p. 4; Appendix E, Proposition E.1
  and Eqs. (E.3)–(E.4).
- Choi conventions and scalar specialization: Appendix B.1,
  Eqs. (B.1)–(B.3), pp. 10–11.
- Counterexample: §2, Eq. (2.4); §4, Eqs. (4.1)–(4.2);
  Appendix C, pp. 13–15.
