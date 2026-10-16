---
bibkey: rbarish2026binarymachine
authors: RBarish-UTokyo
year: 2026
title: NPCompleteness-Lean4 finite binary machine and composition source
url: https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925
doi: null
claim: Concrete finite binary tape machines, counted stack compilation, polynomial transducer composition and exact unary paired input decoding.
strata_touched:
  - D5/S0/Computability/BinaryMachine
license: Apache-2.0
triage: anchor
---

# Finite binary machine supply

## Verified locator

<https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>

The immutable source is revision `3e603e795b44fedcf7d6dd65b7d1e30547ead925`
of RBarish-UTokyo/NPCompleteness-Lean4. The retained module correspondence,
original source hashes, adaptations, full license, NOTICE status and finite
replacement contract are in `docs/reports/licenses/RBarishBinaryMachine.md`
and `RBarishBinaryMachine-LICENSE.txt` in the same directory.

The content port preserves the original mathematical namespace and proof bodies.
The supplied stack programs compile to the supplied finite single-tape binary
machine, including initialization, physical cell operations, output and both
halting decisions. Polynomial time counts local machine instructions. The
unary-prefix slice and StackPair concern only outer paired-word encoding.
No upstream CNF language, SAT-completeness theorem, Cook-Levin development or
Challenge scaffold is retained. Original CNF payloads and their satisfiability
semantics remain the repository's unrestricted Conventional interface.

The upstream declared toolchain is Lean 4.35.0-rc2; this repository uses Lean
4.33.0 and mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
Unequal toolchain pins exclude the package-dependency route. At a change to
this repository's own pin, the finite source/type/semantic comparison and
modulewise replacement contract in the license note determine retirement.
