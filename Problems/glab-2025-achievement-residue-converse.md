---
slug: glab-2025-achievement-residue-converse
bibkey: glabpruswisniowski2025achievement
doi: null
url: https://arxiv.org/abs/2512.17285v1
triage: theorem
motivation_gids:
  - D5/S3/Topology/Measures/AchievementResidueConverseRefutation.result
---

# The original unnormalized achievement-set residue converse

## Problem

Szymon Głąb and Franciszek Prus-Wiśniowski, *Achievement sets – current results and open problems*, arXiv:2512.17285v1, Section 2, Problem 9, PDF p.6. The complete source question, transcribed in preregistration [#23055](https://github.com/the-omega-institute/trureturing/issues/23055), is:

> Let (k₁,…,kₘ;1/n) be a multigeometric series such that kᵢ∈ℕ, Σ={σ₀<⋯<σₙ₋₁} has n elements, none of k₁,…,kₘ is divisible by n, and E(k₁,…,kₘ;1/n) has positive Lebesgue measure. Is it true that the set of remainders tᵢ<n with σᵢ≡tᵢ (mod n) equals {0,1,…,n−1}?

The same question appears in Szymon Głąb and Mateusz Kula, *Kenyon theorem revisited*, arXiv:2508.19454v1, Section 5.1, Problem 1, PDF p.18. These source aliases identify one target.

### Statement echo

For every $m\in\mathbb N$ with $m>0$, indexed coefficients $k:\operatorname{Fin}(m)\to\mathbb N$ and $n\in\mathbb N$, define

$$
\Sigma(k)=\left\{\sum_{i\in\operatorname{Fin}(m)}\varepsilon_i k_i:\varepsilon:\operatorname{Fin}(m)\to\{0,1\}\right\},\qquad
 a_t=\frac{k_{t\bmod m}}{n^{\lfloor t/m\rfloor+1}},
$$

$$
E(k,n)=\left\{x\in\mathbb R:\exists A\subseteq\mathbb N,\ \operatorname{HasSum}\bigl((a_t)_{t\in A},x\bigr)\right\}.
$$

Here the coefficient subscript includes the proof that $t\bmod m<m$. Equal coefficients at distinct indices remain independently selectable; $\Sigma$ identifies only equal sum values. The first denominator exponent is one. `blockSums`, `sourceTerm` and `achievement` are these three definitions.

The closed proposition `claim` is the complete universal assertion

$$
\forall m>0\ \forall k:\operatorname{Fin}(m)\to\mathbb N\ \forall n\in\mathbb N,\quad
\Bigl[(\forall i,\ k_i>0)\land \operatorname{Antitone}(k)\land n>1\land
 |\Sigma(k)|=n\land(\forall i,\ n\nmid k_i)\land\lambda(E(k,n))>0\Bigr]
\Longrightarrow \{s\bmod n:s\in\Sigma(k)\}=\{0,\ldots,n-1\}.
$$

`Antitone` means weakly decreasing, so repeated entries are allowed. The $n>1$ condition expresses the source ratio $1/n\in(0,1)$. There is no primitive, gcd-one, normalization or distinct-coefficient hypothesis.

The closed theorem `result : ¬ claim` proves exactly

$$
\neg\!\left(\forall m>0\ \forall k:\operatorname{Fin}(m)\to\mathbb N\ \forall n\in\mathbb N,\quad
\Bigl[(\forall i,\ k_i>0)\land \operatorname{Antitone}(k)\land n>1\land
 |\Sigma(k)|=n\land(\forall i,\ n\nmid k_i)\land\lambda(E(k,n))>0\Bigr]
\Longrightarrow \{s\bmod n:s\in\Sigma(k)\}=\{0,\ldots,n-1\}\right).
$$

## Motivation

The question connects the Lebesgue measure of an actual infinite subsum set to the arithmetic residues of one finite indexed block. Keeping the original coefficients matters because positive measure survives nonzero scaling while the modular residue question can change.

## Gap

The target is the original unnormalized implication. A finite block computation alone does not show positive measure of the original achievement set. The required bridge establishes convergence and realizes every base-six digit sequence by a subset of the original term indices, in both directions and including endpoints.

## Route

Use $m=3$, $k=(9,3,3)$ and $n=6$. For independently selectable bits $u,e,f$, the block value is $9u+3e+3f=3(3u+e+f)$. The digit $3u+e+f$ runs through every integer from zero to five. For $d\in\{0,\ldots,5\}$, choose $u=\mathbf1_{3\le d}$, $e=\mathbf1_{1\le d\bmod3}$ and $f=\mathbf1_{d\bmod3=2}$. The two positions of coefficient three remain distinct.

In `D5/S3/Topology/Measures/AchievementResidueConverseRefutation.lean`, `weight_summable`, `source_summable` and `selected_summable` establish genuine convergence. `selected_hasSum` regroups arbitrary selected subseries through `Nat.divModEquiv 3` and identifies their sums with $3\operatorname{Real.ofDigits}(d)$. `digitSelection_digits` gives the reverse realization of each digit sequence. `achievement_interval` applies `Real.ofDigits_SurjOn`, `Real.ofDigits_nonneg` and `Real.ofDigits_le_one` to prove $E((9,3,3),6)=[0,3]$. The theorem `result` uses `Real.volume_Icc` for positive Lebesgue measure and the missing residue one for the contradiction.

The selection uses the existing `Set.boolIndicator` construction directly. The four public definitions and the sole public theorem have complete authored Blueprint statements; the result states the entire negated proposition and acknowledges the primary source Library note.

## Falsifier

The implication is refuted by the single tuple $(9,3,3)$ at base six. A defect in the stated indexed source model, the convergence/digit realization, either inclusion of the interval equality, or any premise of the original question would invalidate this proposed resolution. A prior equal-or-stronger answer or another exact registered owner would defeat a claim of a new public resolution, without changing the proved formal negation.

## Evidence

The Lean kernel checks the closed `result : ¬ claim`. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}. The proof uses genuine `HasSum`, not a finite truncation or an assumed attractor identification.

The two complete source notes are `Library/Topology/glabpruswisniowski2025achievement.md` and `Library/Topology/glabkula2025kenyon.md`, each with fixed-version primary, source-archive and PDF locators. Their bounded source qualification and literature readings are attributed to the independent Codex CLI source/API seats recorded in #23055. They do not establish exhaustive current openness, novelty or publication priority. The attributed bounded literature screen includes Nitecki arXiv:1106.3779v2 Proposition 12; Banakh et al. arXiv:1403.0098v1 Theorems 1.3(1), 2.1(1) and Corollary 2.2; relevant contexts of arXiv:2603.11310v1, arXiv:2609.24623v1 Theorems 1.2–1.3 and reductions/remarks, arXiv:2510.21878v1 and arXiv:2512.17761v1. These are literature context, not additional Lean prerequisites. The original journal texts of Nitecki (2015) and Kenyon (1997) have not been fully read.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). It is the only authored public theorem. The module's proof shape is `bind-only`, its admission basis is `open-problem-resolution (#23055; Refuted)`, and `escape_witness` is null. Private helpers serve the infinite achievement proof or the final contradiction. No companion theorem or Reg module is supplied.

## Triage

- **Proved in prose — all source premises at the witness.** $m=3>0$, $n=6>1$, and $9\ge3\ge3>0$. Neither nine nor three is divisible by six. The source terms decrease within a block and across its boundary because $3/6^{j+1}\ge9/6^{j+2}$. This also retains independent repeated positions.
- **Proved in prose — exact block cardinality.** When $u=0$, $3u+e+f$ gives $0,1,2$; when $u=1$, it gives $3,4,5$. Thus $\Sigma=\{0,3,6,9,12,15\}$ has exactly six elements. This is a finite derivation, not an experimental reading.
- **Kernel-checked — actual infinite convergence.** `weight_summable`, `source_summable` and `selected_summable` prove summability for the witness and every subset of the original indices.
- **Kernel-checked — both indexed digit bridges.** `selected_hasSum` gives every selected sum its digit representation; `digitSelection_digits` realizes every digit sequence through original independent index selections. `digitBits_right` supplies the finite digit right inverse.
- **Kernel-checked — exact infinite achievement set and endpoints.** `achievement_interval` states $E((9,3,3),6)=[0,3]$, with both inclusions.
- **Proved in prose — positive volume.** The interval equality gives $\lambda(E)=\lambda([0,3])=3>0$. The final theorem's local `hmeasure` uses `Real.volume_Icc` for this same premise.
- **Proved in prose — exact residues and missing residue.** Reducing the six listed sums modulo six gives precisely $\{0,3\}$, so one is absent. The final theorem's local `hmissing` verifies the missing residue.
- **Kernel-checked — full original implication is false.** `result` states the literal closed negation of `claim`, retaining every universal quantifier and source condition. The two source aliases have one resolution.
- **Proved in prose — scaling boundary for this tuple.** Each original term is three times the corresponding term for $(3,1,1)$ at base six. Multiplication by three and division by three send convergent subseries to convergent subseries on the same selected indices, in inverse directions. Thus $E((9,3,3),6)=3E((3,1,1),6)$; dilation multiplies Lebesgue measure by three, preserving its positivity. Division by three changes the block sums to $\{0,1,2,3,4,5\}$ and therefore changes the residue answer modulo six. This explains this instance without asserting an additional Lean family theorem.
- **Open — primitive and normalized variants.** No assertion requiring gcd-one coefficients, nor a statement allowing normalization before testing residues, is settled by `result`.
- **Open — prime-cardinality variant and printed Nitecki endpoint.** No prime-cardinality classification is asserted for the original coefficients. The surrounding printed interval endpoint is not used; only the independently proved $[0,3]$ equality is claimed for this source convention.
- **Open — exhaustive literature, priority and ownership clearance.** The bounded indexed searches and inspected papers do not exclude unindexed synonyms, index lag, off-arXiv corrections or unread journal results. No official acceptance or solution credit is asserted.

## ASSUMED-UNVERIFIED

The source-to-model reading and bounded literature qualification are inherited attributed evidence, not a fresh reading of every cited journal original. The source's printed Nitecki scale and prime-cardinality remark are not hypotheses of the proof. Primitive/normalized questions, a uniform family theorem, exhaustive worldwide priority and absence of off-arXiv resolutions remain unverified. Final independent triplet review, exact-head required CI, normal merge and the exact first dev-push check are separate delivery obligations.
