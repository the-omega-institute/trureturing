---
bibkey: local2026productabsorption
authors: Task-supplied local unpublished mathematical inputs
year: 2026
title: "The scalar product absorption inequality for binary qubit entropy; A sharp physical record bound for complex product seeds"
doi: null
url: https://github.com/the-omega-institute/trureturing/blob/a5f1b8485c7373d7943fc33aab7d6abb5f1819f7/Library/Entropy/local2026productabsorption.md
claim: "The scalar input gives a logarithmic integral proof of the closed-domain binary-entropy product absorption inequality. Its kernel lemma proves the exact quartic single-crossing property. The independent product-seed input constructs the explicit sharp noise-record comparison channel."
strata_touched:
  - D5/S3/Entropy/ProductAbsorptionLogKernel
  - D5/S3/Entropy/ProductAbsorptionLogIntegral
  - D5/S3/Entropy/BinaryEntropyLogIntegral
  - D5/S3/Entropy/ProductAbsorptionLogMoment
  - D5/S3/Entropy/ProductAbsorptionScalar
license: citation-only
triage: anchor
---

# Local unpublished product absorption proofs

These are local unpublished ordinary mathematical inputs, not published
theorems, independent formal certificates, or evidence of worldwide priority.
The Lean statements and their kernel-checked proof terms determine the
formal scope.

## Verified locator

Immutable sourcepack attribution note: https://github.com/the-omega-institute/trureturing/blob/a5f1b8485c7373d7943fc33aab7d6abb5f1819f7/Library/Entropy/local2026productabsorption.md
This URL identifies the preserved sourcepack and its attribution, not a
published version of either ordinary proof or an independent certificate.

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

The logarithmic integral module (`ProductAbsorptionLogIntegral`) is an
**UNCOMPILED SOURCE ATTEMPT / OUTSIDE THIS UNIT'S VERIFIED SCOPE**. Its source
attempt uses the primitive
`(s+x)log(s+x)-slog(s)`, whose derivative is `log(1+x/s)` for `s>0`.
After subtracting `xlog(s)` it lies between `x` and `x+x^2/s`.
The first-order coefficient cancellation gives the exact moment as the
improper integral. The single-crossing theorem supplies absolute
integrability by separate nonnegative and nonpositive derivative FTC
arguments. Nonnegativity of that moment is a separate obligation.

The binary-entropy integral module (`BinaryEntropyLogIntegral`) is an
**UNCOMPILED SOURCE ATTEMPT / OUTSIDE THIS UNIT'S VERIFIED SCOPE**. Its source
attempt uses the actual natural-logarithm
`Real.binEntropy` and the exact integrand
`log(1+x/s)/sqrt(1+s)`. Its closed-domain target includes `x=0,1`.
The continuous primitive with `r=sqrt(1-x)` and `y=sqrt(1+s)` is
`2ylog(s+x)-2slog(s)/(y+1)-4log(y+1)+2r(log(y+r)-log(y-r))`.
Its limit at infinity is zero and its value at zero is minus four times
the binary entropy. The nonnegative-derivative improper FTC gives the
integral identity and absolute integrability together.

The kernel theorem includes the entire closed parameter square. Its
boundary reduction uses the zero kernel at one zero parameter and the
identity
`(1+v/s)(1+(1-v)/s)-(1+1/s)=v(1-v)/s^2`
at one unit parameter, together with symmetry.

The original entangled-seed and mixed-seed quantum question is outside this
product component. No numerical check is used as a universal proof.

The first-moment module (`ProductAbsorptionLogMoment`) is an
**UNCOMPILED SOURCE ATTEMPT / OUTSIDE THIS UNIT'S VERIFIED SCOPE**. Its source
attempt normalizes the two parameters by their sum and
uses the root-pair logarithmic curvature estimate
`g_d''(s)>=2/(3s)`. The normalized gap is concave between two explicitly
nonnegative entropy endpoints. Exact scaling returns the original moment;
symmetry and direct edge evaluations include the entire closed square.

The scalar module (`ProductAbsorptionScalar`) is an
**UNCOMPILED SOURCE ATTEMPT / OUTSIDE THIS UNIT'S VERIFIED SCOPE**. Its source
attempt combines the actual entropy integral, that nonnegative
moment and the exact single-crossing theorem. The decreasing weight
`1/sqrt(1+cs)` preserves the sign of the integral. The substitutions
`u=1-z^2`, `v=1-w^2`, `c=1-b^2` return the precise binary-entropy inequality,
with both root orderings and every closed-domain boundary. The sharp
noise-record envelope and actual density-state endpoint are separate
quantum obligations; no entangled- or mixed-seed extension is asserted.

The fixed full product-seed absorption goal remains open: the complete
closed-domain scalar H inequality, the explicit sharp D* record-channel
bridge, and the actual spectral-entropy/density/channel endpoint d<=J_A
are not established by this kernel unit. The four source attempts are
preserved separately in the immutable sourcepack; their descriptions above
state intended arguments and carry no compilation or acceptance claim.
