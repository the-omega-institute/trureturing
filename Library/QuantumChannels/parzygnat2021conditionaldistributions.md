---
bibkey: parzygnat2021conditionaldistributions
authors: Arthur J. Parzygnat
year: 2021
title: "Conditional Distributions for Quantum Systems"
doi: 10.4204/EPTCS.343.1
url: https://arxiv.org/abs/2102.01529v3
claim: "For a density matrix ν on M_m ⊗ M_n with invertible marginals ρ and σ, the conditional domains B_ν = {B : [ρ, tr_B(ν(1 ⊗ B))] = 0} and A_ν = {A : [σ, tr_A((A ⊗ 1)ν)] = 0} are operator systems (Definition 5.5, Lemma 5.8); they need not be C*-subalgebras for m = n = 3, and the author suspects that they always are for 4 × 4 density matrices (footnote 13)."
strata_touched:
  - D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation
license: citation-only
triage: anchor
---

# Parzygnat, conditional distributions for quantum systems

A. J. Parzygnat, *Conditional Distributions for Quantum Systems*, in M. Backens and C. Heunen (eds.), Proceedings 18th International Conference on Quantum Physics and Logic (QPL 2021), Electronic Proceedings in Theoretical Computer Science 343 (2021) 1–13, DOI 10.4204/EPTCS.343.1; arXiv:2102.01529 [quant-ph] (v1 2 February 2021, v2 30 May 2021, v3 13 September 2021).

## Verified locator

DOI: 10.4204/EPTCS.343.1

Source: https://arxiv.org/abs/2102.01529v3; the text was read from the PDF. Versions v1 and v2 were compared for the statements below.
- page 6: Corollary 4.5 (the conditionals F and G for invertible marginals);
- page 9: Lemma 5.1 (∗-preservation criteria);
- page 10: Definition 5.5 (the commutants and the conditional domains), Lemma 5.8 (operator systems), Example 5.10, the remark on the 9 × 9 counterexample, and footnote 13.

Footnote 13 has the same wording in all three versions; it is footnote 12 in v1.

## Source statements

Corollary 4.5: "Set A := M_m(C) and B := M_n(C). Let ζ ≡ tr(ν · ) be a state on A ⊗ B (with density matrix ν) whose marginals on A and B are given by ζ ∘ ι_A =: ω ≡ tr(ρ · ) and ζ ∘ ι_B =: ξ ≡ tr(σ · ), respectively. Suppose that ρ and σ are invertible."

Definition 5.5: "Set A^ρ_c := {A ∈ A : [ρ, A] = 0} and B^σ_c := {B ∈ B : [σ, B] = 0} to be the commutants of {ρ} and {σ} inside A and B, respectively. Set B_ν := {B ∈ B : tr_B(ν(1_m ⊗ B)) ∈ A^ρ_c} and A_ν := {A ∈ A : tr_A((A ⊗ 1_n)ν) ∈ B^σ_c} to be the conditional domains of ν inside B and A, respectively."

Lemma 5.8: "In the notation of Definition 5.5, B_ν and A_ν are operator systems."

After Example 5.10: "Example 5.10 suggests that B_ν and A_ν are not only operator systems, but they might even be C∗-subalgebras. Is this always the case? The answer to this question is no, though the simplest counterexample I could currently find involves a 9×9 rank 2 density matrix with A = M3(C) and B = M3(C). Its expression is not particularly enlightening, so I have chosen to not record it here."

Footnote 13: "Also, I could not find a 4 × 4 density matrix ν for which the conditional domains are not C∗-subalgebras, and I suspect that this may always be the case. I hope to resolve this in future work."

## Reading used by the repository

A 4 × 4 density matrix with both factors nontrivial is a two-qubit state, m = n = 2, with invertible marginals as in Corollary 4.5. An operator system in M₂(ℂ) containing 1 is a C*-subalgebra exactly when it is closed under multiplication, since a finite-dimensional *-subalgebra is norm-closed. The repository states the suspicion as: for every two-qubit density matrix with invertible marginals, both conditional domains are carriers of unital star subalgebras of M₂(ℂ).
