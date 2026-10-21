---
slug: chirvasitu-cusick-2024-rules-matrix-order-conjecture-6-1
bibkey: chirvasitucusick2024quadraticrotation
doi: 10.1016/j.dam.2023.10.010
url: https://arxiv.org/abs/2304.12734v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.result
---

# A sign obstruction to Chirvasitu–Cusick Conjecture 6.1

## Problem

A. Chirvasitu and T. W. Cusick, *Quadratic rotation symmetric Boolean functions*, arXiv:2304.12734v1, Section 6, Conjecture 6.1:

> For i > j ≥ 1 the eigenvalues of the matrix R(i, j) of (6-3) are all √2-scaled roots of unity. Moreover, the multiplicative order of R(i,j)/√2 is precisely 2 · lcm(4, i − j, i + j).

The source and its definitions are recorded in [the Library note](../Library/Fourier/chirvasitucusick2024quadraticrotation.md). The preregistration is [#19397](https://github.com/the-omega-institute/trureturing/issues/19397). The settlement refutes the conjunction through the order conjunct at $(i,j)=(8,4)$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $H_0=[[1,1],[1,-1]]$, $H_1=[[1,1],[-1,1]]$ | `H0`, `H1` | Integer entries in source order. |
| Append $k$ zero columns after each column | `pad` | Column $b$ reads column $b/(k+1)$ precisely when $b\bmod(k+1)=0$. |
| Rotate every row rightward $k$ times | `rot` | Column $b$ reads column $b-k$ modulo the width; `[NeZero n]` expresses a nonempty cyclic index set. |
| Alternate the blocks in batches of $2^{j-1}$ | `blockH` | Starts with $H_0$, then alternates with $H_1$. |
| Stack the blocks of Eq. (6-3) | `R` | Row $2k+c$ reads row $c$ of block $k$. |
| The same rules matrix over the real numbers | `Rsq` | Row-bound reindexing and the integer-to-real entry map; no altered entries. |
| For all $i>j\ge1$ | `claim`, natural binders and the two inequalities | The source range is retained. The dimension is $2\cdot2^{i-1}=2^i$ throughout this range. |
| Eigenvalues are $\sqrt2$-scaled roots of unity | First conjunct of `claim` | Complex spectrum; a positive exponent may depend on the eigenvalue. |
| Order is precisely $2\operatorname{lcm}(4,i-j,i+j)$ | Second conjunct of `claim` | `orderOf` in the monoid of real square matrices. |
| Refutation of the complete assertion | `result` | The proposition is exactly the negation of `claim`. |

The public definitions agree with the binding definitions in #19397. Integer entries, zero-based finite indices and real scalar multiplication specify the source matrix without extra hypotheses on the conjecture.

## Motivation

The order controls the periodicity of the normalized rules matrix $U=R(i,j)/\sqrt2$. Binary transport of Pauli labels does not retain all signs. A scalar identity for a power of $U$ requires those signs as well as the labels.

## Gap

The preregistration records a tier-1 named conjecture and the source and literature checks: arXiv v1, the journal record, later Cusick papers including arXiv:2502.10864, and a targeted search for a settlement. No prior settlement was found in that scope; individual citing records were not all read. Literature-search completeness is `ASSUMED-UNVERIFIED`.

## Route

Use the literal Eq. (6-3) matrix with $(i,j)=(8,4)$ and its $256\times256$ integer reindexing $A$. The private finite certificates give its two nonzero row entries and a signed Pauli transport for 24 steps. The endpoint permutation is the identity, while its phase reverses sign. Applying this transport to coordinate vectors forces every diagonal entry of $A^{24}$ to vanish, hence $\operatorname{tr}(A^{24})=0$.

The asserted order is $2\operatorname{lcm}(4,4,12)=24$. That order would imply $(\sqrt2^{-1}R(8,4))^{24}=I$, hence $R(8,4)^{24}=4096I$, whose trace is $1048576$. The incompatible traces refute `claim`.

## Falsifier

A mismatch with the source's padding, rotation direction, block alternation or row ordering would invalidate the interpretation. Each has a full-body Scribe node and the statement echo above. The proof uses a kernel-checked integer certificate, not the floating order scan. It asserts neither exact order 48 nor the negation of the eigenvalue conjunct.

## Evidence

The canonical module is `D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.lean`. Its public theorem `result` proves the literal negation of `claim`. The private declarations `pauli_power`, `phase_endpoints`, `power_diag_zero`, `trace_power` and `order_ne` supply the signed-transport and trace contradiction. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

The independent checker is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/f6f05757e065d45c0f14bce4085f46b713d78896/docs/reports/chirvasitu-cusick-2023-rules-matrix-order), commit `f6f05757e065d45c0f14bce4085f46b713d78896`, script `check.py`, SHA-256 `f364b6795d229f1352f9ff59f297ef56fe0d08f4b7dbf2ef2ae3933f85e57e78`.

Command in that repository: `OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 python3 docs/reports/chirvasitu-cusick-2023-rules-matrix-order/check.py`; exit 0, `RESULT PASS`.

For $(8,4)$, the integer computation gives $R^{16}\ne2^8I$ with trace 4096, $R^{24}\ne2^{12}I$ with trace 0, and $R^{48}=2^{24}I$. Together these certify exact order 48: an order dividing 48 and different from divisors of 24 or 16 must be 48. The other scan uses floating powers with tolerance $10^{-6}$ over exactly $1\le j<i\le10$; it agrees with the corrected formula throughout that finite range, and its only failure of the conjectured formula is $(8,4)$, with 48 versus 24. The integer Hadamard check covers exactly $1\le j<i\le10$.

## Triage

Tier 1; `theorem`; resolution `Refuted`. The module has `admission_basis: open-problem-resolution (#19397; Refuted)` and computational utility `certified-instance` under `refutes`. There is no digestion atom. Every theorem is classified `bind-only`; the external named settlement supplies admission.

### What the settlement shows

- **Kernel-checked:** the conjecture as the stated conjunction is false at $(8,4)$, by `result` using private `order_ne`. The proof establishes order different from 24.
- **Kernel-checked:** the $Z_0$ Pauli label returns with opposite sign after 24 steps, by private `pauli_power`, `perm_endpoints` and `phase_endpoints`. Private `power_diag_zero` and `trace_power` turn that signed transport into the zero-trace obstruction. Binary labels alone omit the sign needed for the scalar identity.
- **Computed:** exact order 48 at $(8,4)$, by the three integer power comparisons in the experiment entry. Exact order 48 is not formalized here.
- **Computed:** the Hadamard property of $R(i,j)^i$ for exactly $1\le j<i\le10$, and agreement with the corrected order formula in the floating scan over the same range. The experiment entry specifies integer versus floating arithmetic; neither finite check establishes a universal assertion.
- **Open formalization:** the universal Clifford and valuation mechanism. The research seat describes $U$ as a real Clifford operator and locates failures where $\nu_2(i)\ne\nu_2(j)$ and both valuations are at least 2. Only the signed $(8,4)$ transport is kernel-checked here; the universal description and classification are not established by this module.
- **Open formalization:** the research seat's proposed universal correction $\operatorname{ord}(U)=2\operatorname{lcm}(4,i-j,i+j,2\gcd(i,j))$. Its paper-level argument uses real Clifford operators, a binary minimal polynomial and quadratic character sums; that full argument is not reproduced or certified here. The finite floating scan supports only $1\le j<i\le10$.
- **Open formalization:** the universal eigenvalue conjunct. Its proposed derivation from finite order requires a universal finite-order theorem, absent from this module. Refuting the order conjunct does not refute this conjunct.
- **Open:** the full multiplicity structure of the eigenvalues. No multiplicity assertion is made.
- **Scope and source consequences:** the exact proposed order cannot be used universally. The eigenvalue assertion, the Hadamard assertion and any corrected restricted order statement are separate claims; this refutation does not negate them. A result using the conjectured order needs an independent order premise or a corrected proof. No such dependent result is certified by this module.

## ASSUMED-UNVERIFIED

Completeness of the literature search and worldwide novelty or priority. The research seat's universal corrected formula, Clifford description, valuation classification and universal eigenvalue argument are not kernel-checked by this delivery. The floating finite scan is numerical evidence with the stated tolerance and tested range, not a uniform theorem. Mathematical truth is carried by the Lean declarations and their compiled axiom closures.
