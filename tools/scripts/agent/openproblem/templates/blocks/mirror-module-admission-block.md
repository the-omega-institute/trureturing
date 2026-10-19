
## Module admission before freeze (binding, every lane)
For every **supporting** module of the delivery (every module other than the settling one), CLAUDE.md §3.2 requires at least one declaration that is genuine content: an escape witness that survives a compiled bypass. Consumed bind-only helpers do not give a module its own admission.
1. List each supporting module with the witness its header names.
2. For each witness, write a scratch bypass in `.lake/scratch/` (never tracked files) that tries to obtain it from frozen or pinned-Mathlib results by instantiation, projection and normalization only (`simp`, `ring`, `linarith`, `omega`, `norm_num`, `decide`). Report the file and its exit code. A compiling bypass means the witness is bind-only.
3. Inline same-delivery helpers when you judge: a theorem whose proof only applies bind-only helpers of the delivery and rewrites is bind-only.
4. **A supporting module whose declarations are all bind-only is a blocking finding.** The fix is to host its consumed helpers in a module of the delivery that has its own admission, with every file at most 1000 lines. Name the host.
5. Also report every consumed helper that the module header labels content but whose proof is bind-only. That is a blocking label finding with the exact corrected label.
6. The supporting modules are new, so they have no frozen state files; that is expected and is never a reason to skip the bypass. The bypass uses only already-frozen repository declarations on `origin/dev` and pinned Mathlib; it imports the lane's new modules only for the definitions the witness statement needs. Report the results under the key `supporting_module_admission`, one entry per supporting module (file, exit code, first unsolved goal).

## Preregistered conventions are authoritative (binding, every lane)
The preregistration issue's "Lean conventions (binding)" section fixes the public definitions and `claim`.
- Judge fidelity **to those conventions**: a public definition or `claim` that differs from them is a blocking finding.
- Never ask to change a definition or `claim` away from the preregistered form, even toward a more literal transcription of the source. If you find the preregistered convention unfaithful to the source, report that as an advisory with the exact source text, and the orchestrator decides.
- Alternative forms (computational, weighted, or Rayleigh forms) belong in private bridge lemmas consumed on `result`'s path.
