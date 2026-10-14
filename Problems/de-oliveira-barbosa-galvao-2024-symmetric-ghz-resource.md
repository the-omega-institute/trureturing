---
slug: de-oliveira-barbosa-galvao-2024-symmetric-ghz-resource
bibkey: deoliveira2024symmetricghz
doi: 10.22331/q-2024-04-09-1312
url: https://arxiv.org/abs/2212.03668
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.result
---

# Symmetric GHZ resources for complete symmetric Boolean functions

## Problem

M. de Oliveira, L. S. Barbosa and E. F. Galvão, *Quantum advantage in temporally flat measurement-based quantum computation*, arXiv:2212.03668v4, Quantum 8, 1312 (2024), Section 4.2, Conjecture 2:

> The number of qubits in a GHZ state necessary for the deterministic evaluation of a complete symmetric function Cᵏ, of constant degree k, with an n bit input string and a symmetric measurement assignment, scales as Ω(n^{⌊k/2⌋−1}).

The [source note](../Library/QuantumBounds/deoliveira2024symmetricghz.md) quotes Definitions 5, 15 and 16, Equations (70)–(72), and Corollary 1. Issue [#16724](https://github.com/the-omega-institute/trureturing/issues/16724) specifies the mathematical statement and source correspondence.

### Statement echo

All Lean names in this dossier belong to `D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound`.

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| $n$ Boolean inputs | `Fin n → Bool` | Every input, including the all-false input |
| Parity basis on $S$, Eq. (71) | Literal `Odd`-cardinality expression in `layer` | Integer zero or one according to odd subset weight |
| All parity bases of each chosen size, Definition 16 | `layer`, `T : Finset ℕ` | Each selected size satisfies $1\le i\le n$ |
| Equal coefficients within a size, Eq. (72) | `a : ℕ → ℝ`, `ComputesSym` | One real coefficient per size; no constant term |
| Complete symmetric function, Definition 5 | `csf` | Degree-$k$ squarefree monomials counted modulo two |
| Integer lift congruent modulo two, Definition 15 | `ComputesSym` | For every input there is an integer with the required real value and parity |
| One qubit per selected parity basis | `qubits` | $\sum_{i\in T}\binom ni$, including selected zero-coefficient layers |
| Constant degree and asymptotic lower bound | `claim`, `result` | For every $k\ge1$, positive $c$ and threshold $N$ depend only on $k$, uniformly in $n,T,a$ |

There are no additional public hypotheses. The integer exponent in `claim` is $\lfloor k/2\rfloor-1$, including $-1$ for $k=1$. Selected zero-coefficient layers can only increase the counted resource. The precise conventions are the literal expressions in #16724.

## Motivation

The source gives numerical support for Conjecture 2 but no all-degree proof. A uniform lower bound distinguishes the resource needed by symmetric assignments from sparsity estimates that depend only on degree. The stronger finite estimate makes the resource obstruction explicit for every $n\ge k\ge2$.

## Gap

The source and literature checks recorded in #16724 cover the arXiv v4 text, its Appendix G, the journal DOI's seven citing works listed by Semantic Scholar, and the full texts of Bharti–Cabello arXiv:2609.38775 and Grilo–Kashefi–Markham–de Oliveira arXiv:2404.18104 and 2501.07939. None of these checked texts states a proof of Conjecture 2.

The additional readings of Mori arXiv:1803.09947 give degree-based lower bounds, and Frembs–Roberts–Campbell–Bartlett arXiv:2203.09965 give elementary-symmetric upper-bound machinery; neither reading supplies the all-degree symmetric lower bound. These are literature readings, not Lean dependencies. Literature completeness and priority remain `ASSUMED-UNVERIFIED`.

## Route

Put $m=\lfloor k/2\rfloor$ and $r=k-2m$. At Hamming weight $w$, write $E_j(w)$ for the signed parity layer. The Boolean/weight bridge gives $C^k(x)=\binom wk\bmod2$ and $2\operatorname{layer}(n,j,x)=\binom nj-E_j(w)$. Thus an integer lift from `ComputesSym` is a real linear combination of the constant and the $E_i$ with $i\in T$.

The coefficients $d_u=(-1)^{m-u}\binom mu$, supported at weights $2u+r$, satisfy

$$\sum_{u=0}^{m}d_u(1-X)^{2u+r}(1+X)^{n-2u-r}
=(-4)^mX^m(1-X)^r(1+X)^{n-2m-r}.$$

For $m\ge1$ their sum is zero. The right side has no coefficient below $m$ or above $n-m$. Therefore the certificate annihilates the constant and every selected parity layer outside the middle interval. On its support, every integer lift of $C^k$ is even before weight $k$ and odd at weight $k$, so its certificate pairing is odd. This contradicts annihilation unless $T$ contains a middle layer.

A middle layer $j$ costs $\binom nj\ge\binom nm$. The finite estimate and the bound $\binom nm\ge n^m/(2^m m!)$ for $2m\le n$ imply the asymptotic claim. The $k=1$ branch uses the positive resource bound.

## Falsifier

The claim concerns symmetric assignments with one real coefficient per selected size, integer lifts on every Boolean input, and no constant term. A counterexample must satisfy all these conditions and violate the uniform lower bound. Arbitrary nonsymmetric assignments are outside the statement. The physical GHZ interpretation uses the source's NMQC correspondence; it is not an additional Lean theorem about laboratory states or measurement operations.

## Evidence

The source is [SymmetricGHZResourceLowerBound.lean](../D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.lean). The only public theorem is `result : claim`. Its live proof uses the private theorem `finite_lower_bound`, which states $\binom n{\lfloor k/2\rfloor}\le\operatorname{qubits}(n,T)$ for $2\le k\le n$ under `ComputesSym`. The supporting certificate identities and obstruction are kernel-checked private declarations, rather than additional public settlement claims.

The axiom closure of every public declaration is contained in {`propext`, `Classical.choice`, `Quot.sound`}. The proof reuses the frozen D5 owners `SingleRunDegrees.singleRun`, `SparseLiteralParityReadLowerBound.parity` and `LorentzLowDegreeCoefficientRemainder.populationGenerating`, together with pinned Mathlib. It has no `sorry`, new axiom or diagnostic command.

The four-slot escape audit for `result` is unfinished and tracked in [#16852](https://github.com/the-omega-institute/trureturing/issues/16852). No Reg mirror or `declared_validated` registration is asserted. The missing evidence is a lawful enrolled readout preserving the complete quantified claim, with compiled realization, equivalence and whole-family variation/sensitivity proofs.

### Exact integer experiment

The experiment is [check.py and its results directory](https://github.com/the-omega-institute/trureturing-experiments/tree/ddd4892e087ee7bf6f82082be8a44d37def57e78/docs/reports/de-oliveira-barbosa-galvao-2024-symmetric-ghz-resource), pinned to commit `ddd4892e087ee7bf6f82082be8a44d37def57e78`. Command: `python3 docs/reports/de-oliveira-barbosa-galvao-2024-symmetric-ghz-resource/check.py` from that experiments checkout. Script SHA-256: `0228981f6d932eb666745838b16ae2c9e881a860b03be5aa6110ce4f64d131af`; exit 0, `ALL_OK`.

The tested scope is exactly all 276 pairs $2\le k\le n\le24$. In exact integers it checks agreement of the Krawtchouk form with the direct signed sum, annihilation of the constant and all layers $j<m$ or $j>n-m$, and the odd certificate pairing of the complete symmetric function. This computation is independent finite evidence; the unbounded theorem is justified by the Lean proof.

## Triage

Tier 1, resolution **Proved**, admission `open-problem-resolution (#16724; Proved)`.

### What the settlement shows

- **Mechanism — kernel-checked.** `csf_weight`, `layerPolynomial_weight`, `layerPolynomial_coeff` and `layer_signed` give the weight and signed-layer bridges. `parity_eq_owner` identifies the literal subset parity with the frozen Boolean parity owner. `certificate_sum`, `certificate_generating`, `certificate_coeff`, `certificate_layer` and `certificate_odd_pairing` establish zero constant pairing, annihilation outside $[m,n-m]$, and odd lift pairing. `middle_layer_obstruction` forces $j\in T$ with $m\le j\le n-m$. `choose_le_of_middle` and `finite_lower_bound` give cost at least $\binom nm$. These are private declarations on `result`'s proof path.
- **Strength — kernel-checked lower bounds.** `finite_lower_bound` proves the finite binomial estimate. `choose_power_lower` proves $n^m/(2^m m!)\le\binom nm$ for $2m\le n$. `result` proves the source's exponent $m-1$; its proof chooses $c=1/(2^m m!)$ and $N=2k$ for $k\ge2$; `qubits_pos` handles $k=1$.
- **Strong asymptotic consequence — proved in prose.** Fix $k\ge2$ and put $m=\lfloor k/2\rfloor$. For every $n\ge k$, $2m\le n$ and the two kernel-checked estimates give $\operatorname{qubits}(n,T)\ge\binom nm\ge n^m/(2^m m!)$. The constant $1/(2^m m!)$ is positive and independent of $n,T,a$, giving $\Omega(n^m)$ for this family, one power stronger than Conjecture 2. There is no separate Lean theorem stating that asymptotic notation.
- **Binomial order — proved in prose.** For fixed $m\ge1$, $\binom nm=n(n-1)\cdots(n-m+1)/m!\le n^m/m!$. Combined with the kernel-checked lower estimate for $n\ge2m$, this gives $\binom nm=\Theta(n^m)$. No Lean theorem in this module states a separate two-sided asymptotic equivalence.
- **Other constant-degree symmetric families — open.** Source Corollary 1 states that its reduction extends the conjectural lower bound to every constant-degree symmetric Boolean family. Conjecture 2 supplies the complete-symmetric premise of that published consequence. The corollary's family reduction is a published consequence, but its extension is not separately checked or formalized here; the broader family remains open for this delivery.
- **Constant phase offsets — proved in prose.** Adding a constant $b$ to a lift adds $b\sum_ud_u=0$ to the pairing when $k\ge2$. The same contradiction therefore gives the finite bound for that extended model. The public `ComputesSym` remains the no-constant predicate; there is no separate Lean theorem for the extension.
- **Matching upper bound — open.** A construction reported with cost at most $2\sum_{j\le m}\binom nj$ is unverified. The lower bound alone does not establish sharpness or an achievable resource scaling.
- **Nonsymmetric assignments — open.** The proof uses equal coefficients within a size. No lower bound for arbitrary nonsymmetric assignments is claimed.
- **Experiment — computed.** The exact integer experiment above verifies the stated identities and pairing for all 276 pairs $2\le k\le n\le24$, with the pinned script, command, exit code and SHA-256 in its Evidence entry.
- **Literature — literature reading.** The checked Mori and Frembs–Roberts–Campbell–Bartlett results do not supply this all-degree lower bound. Completeness and priority are `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Literature completeness and priority; the physical GHZ/NMQC correspondence beyond the binding mathematical conventions; the source's reduction to other constant-degree symmetric families beyond this complete-symmetric Lean theorem; the reported matching upper-bound construction. The four-slot escape audit remains unfinished under #16852. No claim is made about nonsymmetric assignments.
