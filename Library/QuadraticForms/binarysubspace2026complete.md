---
bibkey: binarysubspace2026complete
authors: Haobo Ma; Reza Nikandish; Wenlin Zhang
year: 2026
title: "Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate"
doi: null
url: https://github.com/the-omega-institute/binary-subspace-orthogonality
claim: "The PR1 all-subspace six-dimensional graph has chromatic number fifteen; the line graph has chromatic number twelve."
strata_touched:
  - D5/S3/Combinatorics/Orthogonality/SixBitCatalogue
  - D5/S3/Combinatorics/Orthogonality/SixBitCatalogueData
  - D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification
  - D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge
license: research-material rights unresolved; original supplied source attribution preserved
triage: anchor
---

# Exact six-dimensional source

The complete received source is the PR1 research version, not the historical
September main manuscript or the later focused/extended versions. The supplied
`formal/Chromatic/Certificate.lean`, `Data.lean`, and `Verify.lean` have original
Git blobs `63c8cf0b8659ed33431f82efbd3cb602d1384c41`,
`ff2985aab91126a2ed55992a08e1a32e192be032`, and
`37b51bd6bf45493699b1ea89aec21022878e2e5c` respectively. The catalogue and proof
bodies are reused, with canonical imports and headers. No coloring search or
table regeneration supplies this return.

The research mask space is Fin 64, with XOR addition and the sum of the six
bit-products modulo two. Its full graph uses every zero-containing XOR-closed
finite set except {0}. The canonical bridge maps each low bit to the
corresponding ZMod 2 coordinate, proves addition and dot-zero compatibility,
and maps every complete source space to its actual Submodule. A mask wrapper
provides the actual binary module; it does not use Fin 64's modular arithmetic
as binary vector addition. The nonzero-space and graph equivalences preserve
top, bottom exclusion, distinctness and all cross pairings.

The full source has 2824 nonzero spaces with dimension counts
(63,651,1395,651,63,1), and its catalogue has 2825 entries including zero.
The 44968-edge/3986076-pair counts and independent Python verification remain
attributed reports until actually reproduced. The four original native_decide
obligations are catalogue_covers, catalogue_proper, clique_valid and
clique_adjacent. Historical Lean 4.33.0 provenance includes propext,
Classical.choice, Quot.sound and four native-evaluation axioms. Current
compilation must print the actual current transitive closure; a successful
source transfer does not erase this trust boundary. Generic Catalogue.complete
and Catalogue.colorable have the standard axiom boundary.

PR1 has the separate exact line result twelve, including its weighted
independence proof and literal partition. The September main only had the
12–13 line interval. The September 28 note is credited Wenlin Zhang then
Haobo Ma; the September 29 main and October manuscripts name Haobo Ma,
Reza Nikandish and Wenlin Zhang. The focused October 10 manuscript and extended
October 8 working version are distinct. The extended version is not an
accepted replacement of the focused/submitted draft.

All failed structural color rules, n7 at-least-nineteen results, exact-n7 open
boundary and paused n7 case-exclusion work retain their original status.
Neither a twelve-color line certificate nor a fifteen-color full-space
certificate supplies those higher-dimensional results. Full lift data
reconstruct a subspace, not a universally successful conceptual coloring rule.

The workspace has no selected unified research-material reuse license. This
return follows the supplied source authorization, preserves the authors and
version distinctions, and makes no academic publication, submission, rights,
priority or author-order decision. The older primary Nikandish paper and the
separately licensed clique proof retain their own original attribution.
