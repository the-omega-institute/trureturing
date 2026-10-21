---
bibkey: maityfuruichidutta2026deformed
authors: Srikrishna Maity; Shigeru Furuichi; Supriyo Dutta
year: 2026
title: r-deformed α-z-Rényi relative entropy
doi: null
url: https://arxiv.org/abs/2607.01805v1
claim: Definitions 1–2 and equations (6), (8)–(9), (47) define the deformed logarithm and relative entropies; Section 4 Case 5 asserts the ordering B₁ ≤ B₂ for noncommuting density operators.
strata_touched:
  - D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation
license: citation-only
triage: anchor
---

## Verified locator

Source: https://arxiv.org/abs/2607.01805v1

Definitions 1–2, equations (6), (8)–(9), printed page 2; equations
(46)–(47), printed page 11; Section 4 Case 5, printed page 12.

## Source statements

Definition 1, page 2: “The r-logarithm is denoted by ln_r(x) and it is defined by
ln_r(x) = (x^r − 1)/r, for r ≠ 0 and x ≥ 0.”

Definition 2, page 2: “The r-deformed α-z-Rényi relative entropy for any two
positive semi-definite operators ρ and σ with Supp(ρ) ⊆ Supp(σ) is defined by
D^{(r)}_{α,z}(ρ||σ) = (1/(α−1)) ln_r Tr[(σ^{(1−α)/(2z)} ρ^{α/z}
σ^{(1−α)/(2z)})^z] … where α, r ∈ R and z ∈ R+.”

Equations (8)–(9), page 2: “For 0 ≤ α < 1 and q > (1 − α), we compare two
upper bounds B₁(ρ||σ) = D^{(r)}_{α,z}(ρ||σ) and B₂(ρ||σ) =
−Tr[ρ ln_{1−α}((ρ^{−q/2} σ^q ρ^{−q/2})^{1/q})] of the Tsallis relative
entropy, numerically. We observe that for non-commutative density operators ρ
and σ, D_α(ρ||σ) ≤ B₁(ρ||σ) ≤ B₂(ρ||σ).”

Section 4, Case 5, page 12: “Let Tr(ρ) = 1 and Tr(σ) = 1, that is both ρ and
σ are density operators. Here, we numerically observe that for any two
operators ρ and σ, B₁(ρ||σ) is a tighter bound of Tsallis relative entropy
than B₂(ρ||σ).”

The formula following equation (6) is
`D_α(ρ||σ) = Re Tr[ρ − ρ^α σ^{1−α}]/(1 − α)`.
Matrix functions in the formal statement use real continuous functional
calculus, and matrix traces use their real parts. Positive definiteness and
unit trace give a subclass of the source's density operators on which all
negative powers and support requirements are satisfied. The source's B₁ is
exactly the function named `renyiRZ` in Lean.

## Counterexample and scope

For ρ = diag(4/5, 1/5) and
σ = (1/125)[[28, 6√6], [6√6, 97]], the Lean proof verifies positive
definiteness, unit trace and noncommutation. At α = r = 1/2, z = 2 and q = 1
it proves B₂ < 2/5 < B₁. These parameters occur in the source's Figure 2.
The refutation concerns the second inequality of equation (9). It does not
refute the inequality D_α ≤ B₁, prove an ordering for other parameters, or
refute the commuting comparison in Theorem 2.

The numerical experiment is
`docs/reports/maity-furuichi-dutta-2026-tsallis-bound-ordering/` in
`the-omega-institute/trureturing-experiments`, commit
`7e01d5f0271284d3b56bec188402ec9657c2fdbf`. The recorded SHA256 of `check.py`
is `90243c923231b1a9aa7171d85a534e16606b11fe142ef5ecbb1d14dbaad85805`;
`python3 check.py` returned exit 0 and `RESULT PASS`, as reported in
[the source comparison](https://github.com/the-omega-institute/trureturing/issues/18947).
That report also records the literature screen. Its completeness and the
absence of subsequent corrections are `ASSUMED-UNVERIFIED`.
