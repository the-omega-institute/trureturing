---
bibkey: localproductabsorption
authors: Task-supplied local unpublished mathematical inputs
year: 2026
title: "The scalar product absorption inequality for binary qubit entropy; A sharp physical record bound for complex product seeds"
doi: null
claim: "The scalar input gives a logarithmic integral proof of the closed-domain binary-entropy product absorption inequality. Its kernel lemma proves the exact quartic single-crossing property. The independent product-seed input constructs the explicit sharp noise-record comparison channel."
strata_touched:
  - D5/S3/Entropy/ProductAbsorptionLogKernel
license: citation-only
triage: anchor
---

# Local unpublished product absorption proofs

These are local unpublished ordinary mathematical inputs, not published
theorems, independent formal certificates, or evidence of worldwide priority.
The Lean statements and their kernel-checked proof terms determine the
formal scope.

## Verified locator

The scalar input is `product-scalar-gap-analytic-attempt/proof.tex`, titled
“The scalar product absorption inequality for binary qubit entropy”, under
the supplied `quantum-zhang-yeung-20261030` research directory.
Its SHA256 is
`834fd549f89e7c77038b7b95356f59363bd5d2c16c4ea6ae964be7d22c176e19`.
The relevant ordinary statement is its lemma “One sign change of the
logarithmic kernel”, including the five explicit quartic coefficients.

The physical input is `pure-seed-tensorization-independent-attempt/proof.tex`,
titled “A sharp physical record bound for complex product seeds”, in the
same supplied research directory. Its SHA256 is
`49717b7a977992d5def7e4c02fd256b8ad8c4a18437268d34d48252afbd8caec`.
It supplies the ordinary product-seed envelope and the explicit stochastic
map on the first noise record. That quantum bridge is not a dependency of
the logarithmic-kernel theorem.

## Mathematical attribution and scope

The logarithmic kernel and quartic coefficient argument are taken from the
scalar ordinary input. The formal proof uses the actual natural logarithm
and the two nonnegative quadratic roots, including the coincident case.
It establishes neither the entropy integral representation nor the
nonnegative logarithmic first moment. Those statements, the closed-domain
scalar entropy inequality, and the actual density-channel absorption
endpoint remain separate proof obligations.

The kernel theorem includes the entire closed parameter square. Its
boundary reduction uses the zero kernel at one zero parameter and the
identity
`(1+v/s)(1+(1-v)/s)-(1+1/s)=v(1-v)/s^2`
at one unit parameter, together with symmetry.

The original entangled-seed and mixed-seed quantum question is outside this
product component. No numerical check is used as a universal proof.
