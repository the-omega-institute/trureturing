/- GID: D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/Prelude
   generality: G
   mirror-B: none(waiver:upstream-proof-complete-port)
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   utility: none
   digest: Upstream Prelude support declarations for the finite-field character-sum port. -/

/-
Attributed source: https://github.com/fukubillueda-web/epsilon_FML/blob/
b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed/LanglandsFirstMainLemma/Prelude.lean
License: Apache-2.0; the verbatim upstream LICENSE and original source hashes are in
Library/Arith/epsilonfml2026hassedavenport.md.
Modifications: repository import paths.
The upstream namespace, theorem statements, normalization, and proof structure are
retained. The pinned upstream distribution contains no NOTICE file.
-/

import Mathlib

/-!
# Langlands's First Main Lemma

This repository contains the completed formalization, prepared for the
publication freeze.  During construction and audit,
`references/epsilon_FML.tex` was the repository manuscript path.  That
historical path and the other scaffold declarations retained below remain only
as compatibility metadata for the established public API.  The mathematical
blueprint is fully verified, and no completed node uses temporary proof
scaffolding.
-/

namespace LanglandsFirstMainLemma

/-- Historical version identifier retained for compatibility with the completed blueprint. -/
def blueprintScaffoldVersion : String := "epsilon_FML-2026-08-20"

/-- Historical planned module count `108`, retained for compatibility; the
completed current blueprint contains 113 mathematical nodes. -/
def plannedModuleCount : Nat := 108

/-- Historical repository manuscript path used during construction and audit
of the formalization, retained for compatibility. -/
def authoritativeManuscript : String := "references/epsilon_FML.tex"

/-- Historical compatibility proposition from blueprint construction; no completed node uses it. -/
def PendingTask : Prop := True

end LanglandsFirstMainLemma
