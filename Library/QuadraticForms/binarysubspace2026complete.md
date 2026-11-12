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
  - D5/S3/Combinatorics/Orthogonality/WeightedIndependentBound
  - D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic
  - D5/S3/Combinatorics/Orthogonality/BinaryLineGraph
  - D5/S3/Combinatorics/Orthogonality/SixBitLineTransfer
  - D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift
  - D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry
  - D5/S3/Combinatorics/Orthogonality/SixDimensionalProfiles
  - D5/S3/QuadraticForms/RadicalQuotientIsometry
  - D5/S3/Combinatorics/Orthogonality/OrthogonalitySymmetryObstruction
  - D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction
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
source transfer does not erase this historical trust boundary. The current Lean4.35.0 admission checks the unchanged tables and complete
180800 extension witnesses through45 kernel-checked row blocks, with the
original catalogue assembly and actual Submodule transfer. The current
51-module report SHA256 is
07ee39557e1ad3156849e79f9843d4c3d482267d73116189ea3cd8b50c3e67ca.
It records source equality and only the standard three axioms. Native Scribe,
deposit, all48 header checks and official freezing passed for that increment.
These author checks do not certify whole-result review or final-head CI. Generic Catalogue.complete
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

The distinct O2 line theorem uses the original PR1 `lines.tex` (Git blob
35a78b9854f2e79f91197d2dc3e248f35a863571, SHA256
8d132812bcdf5ead47c9a942cfae40d55f6f6ad0a0d6c7c2b98449bfa1344580)
and literal twelve-color partition (Git blob
54f901d0f02b66abeb09186f184d938f1971eaa5). The manuscript proves the weighted
bound by the Gram matrix J+I on even vectors and, after choosing an odd a,
the orthonormal vectors e+a together with the totally isotropic span of u+a
in a-perp. These original arguments and credit are preserved. The current
formal representation is a universal include-or-omit weighted-subset checker,
with both recursion branches proved sound for arbitrary finite candidate lists.
Its input is all63 nonzero masks, with weights3/4 and a complete bound19;
a second all-even input supplies the extremal profile condition. The numerical
checks, total weight221, every color fiber, and the unchanged literal upper
witness are all required by the actual chromatic proof. A development-time
Python evaluation observed bound19 with35439 recursion nodes (4347 distinct
states); that observation is not Lean or normal acceptance evidence. The current line owner and all-line transport compiled with source-matched
scoped reports and standard axiom closures. Its Scribe and native deposit
checks passed; the later affected-consumer report SHA256 is
b02f04fe93cddab4e1206c243f0d795c38b31bc2d18de8ab5fb86c5ee64a535e5.
These are scoped author checkpoints, not whole-result acceptance. It never runs or
reopens paused n7 case exclusions.

The geometry uses precisely T=span(3,12,48), S=span(1,4,16). Every
actual Submodule, including zero and the whole space, has the unique full
quotient-valued K/P/f representation. Exact H/K source intersections, perfect
annihilator/projection recovery, full fiber counts and the entire X/Y/Z
criterion are retained. The fixed clique has all15 nonzero labels and the
original15/14/11 availability sizes. The complete actual nonclique profile
image has240 elements. The actual entire radical quotient and descended
isometries supply the original line profile/quotient obstruction; the full
orthogonal stabilizer and entire clique-label action supply both original
full-group refutations. The exact original planes span(13,6) and span(9,14)
have equal full K/P, quotient-map rank/image/kernel, and a label-fixing shear
orbit. They refute those proposed coloring rules on the complete graph domain.
No proper-subgroup or auxiliary-choice obstruction is inferred.

The PR1 geometry and lift diagnostics remain distinct finite reports:
240 exact profiles with139 multicolored; quotient-dimension enrichment gives
263 profiles with160 multicolored and alternating status gives no further
split; rank/image/kernel gives1662 groups with160 multicolored, resolving87
of the original139 and leaving52; the requested dimension/value-list encoding
gives836 groups,640 single-color and196 multicolored, with267 patterns crossing
exact K/P domains; exact K/P and complete basis values reconstruct all2809
nonclique vertices. These counts retain the original diagnostic/checker and
report provenance, and are not inferred merely from the new reconstruction
theorem. The omitted-domain line counterexample and the full placement
reconstruction are mathematical statements distinct from these statistics.
The original reports also preserve all earlier failed methods and versioned
unknown search records. Current kernel acceptance of the universal geometry
and exact plane witnesses does not itself reproduce every diagnostic report.

The supplied written n7 proof uses the original basis(3,12,48,65,71,95),
quadratic value counts36/28, all288 even heptads,135 Lagrangians and8505
point/hyperplane incidences. Its universal eight-Lagrangian completion rests
on the written31-point hyperplane argument; the nine explicit partial-spread
controls are not an enumeration of all partial spreads. It yields the written
lower bound19, including the deleted characteristic-line graph. Its capacity,
saturation and characteristic-class deficit restrictions retain their exact
original hypotheses; surviving profiles are necessary, not asserted realized.
The current canonical written lower-bound implementation passed the source-matched45-module report (SHA256 aa51bb24b859aaedf637d4375f1b6a6dc33cc6304ef449c705d903bb0696302c), with only propext, Classical.choice and Quot.sound. It covers all three actual graphs, all full classes and parity, and unique completion of every eight actual finrank-three Lagrangian Submodules. The original explicit trace family proves nonvacuity. All43 new modules passed header checks, Scribe emission, deposit and canonical ledger alignment. These are author/component checks, with full independent review and applicable final-head CI still required. The unfinished registration audit is disclosed precisely in linked issue28398, including exact statements and source hashes; disclosure is not proof, audit completion or a gate waiver. Exactn7 and a
nineteen-color witness remain open; no paused exclusions or new coloring search have
been run by this return.
