---
bibkey: gaddejainkrishnakulkarnisharma2024multientropy
authors: A. Gadde, S. Jain, V. Krishna, H. Kulkarni, and T. Sharma
year: 2024
title: Monotonicity conjecture for multi-party entanglement. Part I
doi: 10.1007/JHEP02(2024)025
url: https://arxiv.org/abs/2308.16247v1
claim: Section 7 asks whether the replica invariant E_n^(q) is positive on all normalized pure states.
strata_touched:
  - D5/S3/Quantum/Information/MultiEntropyPositivityRefutation
  - D5/S3/Quantum/Information/MultiEntropy/CQReplicaCoarseGraining
  - D5/S3/Quantum/Information/MultiEntropy/TripartiteReplicaCoarseGraining
license: citation-only
triage: anchor
---

# Positivity of the multi-entropy replica invariant

## Verified locator

DOI: 10.1007/JHEP02(2024)025
Source: https://arxiv.org/abs/2308.16247v1

JHEP 02 (2024) 025. Section 1.2, printed pp. 6–7, equations (1.10)–(1.11), defines
the replica invariant and the Rényi multi-entropy. The source states:

“Consider m = n^{q−1} replicas, arranged as a q−1 dimensional regular hyper-cubical lattice.”

“The permutation σ_q is taken to be identity and the rest of the permutations are taken to be the generators of independent Z_n symmetries i.e. σ_a = g_a for a = 1, …, q − 1.”

Footnote 2 states:

“Note that in defining the Renyi multi-entropy S_n in equation (1.11), we have tacitly assumed that the quantity E_n^(q) is positive.”

Section 7, printed p. 32, states:

“The definition (1.11) of S_n requires that the quantity E_n be positive definite. In this paper, we did not prove or even discuss this and phrased the monotonicity conjecture in terms of E_n instead. Although we found that E_n is positive in the examples we studied, it would be nice to prove this in general and to see if there is any relation between the positivity of E_n and the coarse-graining monotonicity.”

The scalar positivity question is encoded as positive real part and zero
imaginary part, for every n,q ≥ 2 and every normalized pure state on finite
local bases. The final party is unshifted. The coarse-graining inequalities
(1.13)–(1.15) are statements directly about E and are distinct from this question.

## Classical–quantum coarse graining

For a normalized pure state on finite parties $A,B,C$, suppose that the
$AB$ marginal is block diagonal in a basis of $A$. Write its positive
blocks on $B$ as $T_a$. The blocks may fail to commute. For every
integer $n\ge2$, the theorem `E_eq_trace_tensor_sum_pow` writes the
tripartite replica moment as
$\operatorname{Tr}[(\sum_a T_a^{\otimes n})^n]$.
`E_coarseGraining_all_mergers` proves strict positivity and the three
coarse-graining inequalities of Eq. (1.13) for this state class using the
original contraction for both the tripartite and the merged states.
`renyi_coarseGraining_all_mergers` checks positivity of the merged moments
and the corresponding inequalities for the real logarithm in Eq. (1.11).

Section 3 of the original paper treats diagonal states. Tasuki discusses the
all-state result at $n=2$ and the continuum vacuum result in §2.3.

[Gadde et al., §1.2](https://arxiv.org/html/2308.16247v1#S1.SS2) ·
[Tasuki, §2.3](https://arxiv.org/html/2611.34715v1#S2.SS3)

## Finite tripartite coarse graining

For every integer $n\ge2$ and all finite local spaces, the modulus of the
original tripartite replica moment is bounded by the $n$th power of the
bipartite replica moment for each of the three mergers in Eq. (1.13).
The inequality is homogeneous in the pure-state amplitudes. The entropy
inequality uses the real logarithm when the tripartite moment is positive.

Contracting the unshifted party gives a row transfer $R$ with
$E_n^{(3)}=\operatorname{Tr}(R^n)$. In the entry convention used here,
$R=V^\dagger P V$, where $P$ cycles the first-party strings and
$V^\dagger V=\rho_B^{\otimes n}$. Rectangular trace cyclicity and
Schatten Hölder bound the trace by
$(\operatorname{Tr}\rho_B^n)^n$. Transposition and a shear of the
replica grid give the two remaining mergers.

The original paper treats special states. Tasuki §2.3 describes the
all-state result at $n=2$ and proves bounds in a continuum vacuum
setting. The matrix estimate uses standard trace inequalities. The
compression estimate also follows from the positive-map results of
Bourin and Lee (Proposition 1.2) and Watrous (Theorem 1). The application
here establishes the absolute bound for the original finite replica
contraction at all integer orders and arbitrary finite local dimensions.
Priority beyond the reviewed sources remains undetermined.

[Gadde et al., Eq. (1.13)](https://arxiv.org/html/2308.16247v1#S1.E13) ·
[Tasuki, §2.3](https://arxiv.org/html/2611.34715v1#S2.SS3) ·
[Bourin and Lee](https://arxiv.org/abs/1911.10573v1) ·
[Watrous](https://arxiv.org/abs/quant-ph/0411077v1)
