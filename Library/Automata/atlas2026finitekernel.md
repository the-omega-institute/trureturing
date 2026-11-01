---
bibkey: atlas2026finitekernel
authors: ATLAS contributors; Meta Platforms, Inc. and affiliates
year: 2026
title: "Automatic sequences: finite kernels and the Eilenberg bridge"
doi: null
url: https://github.com/facebookresearch/atlas-lean/blob/8c9ac8ce7d2febf34a232009e1e1b0a350174591/MathlibExt/Combinatorics/Words/Automatic.lean
claim: "For every finite B : Type, every natural k and every sequence a : Nat to B, finite arithmetic k-kernel automaticity is equivalent to a positive finite DFAO correct on every LSDF representation, with k at least two on both sides."
strata_touched:
  - D5/S0/Automata/FiniteKernelDFAO
license: "Apache-2.0 with the preserved ML intended-use preface"
triage: anchor
---

# Source of the finite-kernel/DFAO construction

The source theorem is
`MetaMathlibExt.isKAutomatic_iff_isKAutomaticSequence`.
The mathematical result is Eilenberg's characterization, not a new theorem
or a new proof credited to this integration. The proof constructs a machine
from the kernel, establishes its fold invariant, and bounds the reverse
kernel by the image of the finite state set using fixed-length residue words.

## Verified locator

https://github.com/facebookresearch/atlas-lean/blob/8c9ac8ce7d2febf34a232009e1e1b0a350174591/MathlibExt/Combinatorics/Words/Automatic.lean

The immutable source supplies the two kernel definitions and the live
construction from `chr_kernel_lam_mem` through the equivalence, lines 103–305.
The only declarations retained from
https://github.com/facebookresearch/atlas-lean/blob/8c9ac8ce7d2febf34a232009e1e1b0a350174591/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean
are `baseWordValueLSD` and `IsKAutomaticSequence`.
The source files have SHA-256
`9483b621d4da1119219a7c46ed34f1483e66050c7a3f0b4c51c1550021b93385`
and `139cab8fb3f57b2d79b3f474724da8c34bba422e4cd8a8227f4bd7f00e72527d`.

## Scope and attribution

The transplant retains 16 declarations, original proof bodies and finite
`B : Type` scope. Both automaticity predicates require `2 ≤ k`.
The machine has `q > 0` states and must compute the sequence on every
least-significant-digit-first digit word of the given value. Empty words,
all-zero words and trailing high-order zero padding are included. Output
invariance does not require an initial-state zero self-loop. No arbitrary
output type, MSDF, or canonical-only extension is asserted.

Meta Platforms, Inc. and affiliates retain copyright and all rights reserved.
The complete 11,463-byte root license, including the intended-use preface,
is the tracked regular file
`docs/reports/lovasz-suppliers/atlas-LICENSE.txt`, SHA-256
`fc78801eadec58b04e0d5cabe735eb6808e23f47b0cb92b89b55792019b54131`.
It is byte-identical to the supplied revision's root LICENSE. The complete
exact-revision source-tree scan finds no NOTICE file. This mathematical
verification and integration supplies no ML model training, fine-tuning,
distillation, evaluation or development pipeline; preserving the source
notice makes no general legal-clearance claim.

## Compatibility and retirement

The supplied source and consuming repository use Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The source is integrated as a
narrow A17.2 transplant, with no dependency changes. Modifications combine
the retained declarations in the canonical D5 namespace, remove upstream
module/public-section wrappers and make the digit-lemma import explicit.
No unrelated morphic-word library or power-base kernel lemmas are included.
Retire this transplant and use direct reuse when this repository's actually
adopted Mathlib pin supplies an equivalent full finite-alphabet,
all-LSDF-word theorem, including zero and padding.
