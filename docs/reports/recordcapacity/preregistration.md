# Record capacity: preregistration

Base: `5634f82fdcf3f8970ba9501cdcce1de5f2536976`.
Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d` (v4.33.0).
Implementation: Codex with lean4 skill, single worker; independent review belongs to caller.

Delivery shape: **2 (degenerate)**, with a sharper conditional structural corollary if completed.
The unconditional algebraic target is the number of nonzero equivariant idempotents
summing to identity bounded by the complex finrank of the actual commutant of U.
Shared symmetry U and record equivariance remain explicit hypotheses.
This is not a bound on arbitrary record structures and does not derive physical inputs.
No new axiom or instance declaration. No theory ingestion or PR creation.

Proposed `proof_shape: content`, `admission_basis: escape-witness`.
Proposed live witness: sum of the ranks of the ranges of an idempotent resolution
is the dimension of its carrier; each nonzero summand has positive rank.
Use `LinearMap.IsProj.trace` and trace linearity directly, then sum the positive ranks.
This is the counting step, not a reproving of the structural theorem.
Apply to the commutant's faithful left regular action for the guaranteed delivery.
The sharper corollary uses an explicit commutant equivalence to product matrix blocks,
embeds these as a block diagonal action, and counts in dimension sum_i m_i.
It does not by itself identify those block sizes with a caller's irrep multiplicities.
If completed, invoke upstream Wedderburn–Artin under semisimplicity of the commutant
to produce such block data. No semisimplicity claim from a general group action.

Pre-implementation searches:
- D5: commutant / orthogonal idempotent / RecordCapacity: no capacity theorem;
  WindowRegister.window_commutant_eq_scalars is a different, specific rigidity theorem.
- Mathlib RingTheory/SimpleModule: hits
  IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end,
  IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed,
  IsIsotypicOfType.linearEquiv_fun and isotypic decomposition endAlgEquiv.
- Mathlib RingTheory/Idempotents: OrthogonalIdempotents and complete families,
  mapping and central corner decomposition, no counting theorem in searched file.
- Mathlib LinearAlgebra: LinearMap.IsProj.trace, IsIdempotentElem.trace_eq_zero_iff,
  Matrix.blockDiagonal'RingHom, Matrix.blockDiagonal'_injective, Algebra.lmul_injective.
- GitHub code search (authenticated gh): OrthogonalIdempotents + linearIndependent
  gives three TauCeti files. Opened pinned LinearIndependent.lean: the exact
  nonzero-idempotent linear independence theorem already exists there. Do not reprove it.
  That route is not selected; the trace/range-rank counting result is different.
- GitHub idempotents/card/finrank and orthogonal/idempotents/trace searches performed;
  inspected TauCeti FDRep and CharacterTable/IdempotentDecomposition. Those results
  are character decompositions or central-idempotent bases, not the requested bound.
  Search is bounded, not an assertion of global absence.

Computational content: `none`: universally quantified algebraic inequalities,
not a finite enumeration, checker, numeric reduction, or certified finite instance.
The five supplied finite configurations will be recomputed only as diagnostics.

Stop criteria:成 requires kernel proof, serial build sentinel failed=0, lean-report,
emit, scribe-content-checks with exact merge-base, deposit-uncovered, commits and push.
翻 requires a kernel counterexample. Otherwise blocked with completed portion,
failed routes and sharp remaining subproblem. PR and merge remain caller-owned.
