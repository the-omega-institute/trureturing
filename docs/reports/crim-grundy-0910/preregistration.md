# CRIM Conjecture 3 implementation — preregistration v1

Before any mathematical probe or implementation, proposed escape_witness: the paper-specific partition move graph (delete any row; conjugate, delete any row, conjugate back), an SG evaluator descending by cell count, and its correctness on the entire reachable finite DAG. Every option value must be derived from terminal states; no table of twelve prescribed values is an assumption. Expected sample: R^5_{7,6}; the supplied 377 states / depth 12 / value 1 are predictions to test, not input facts.

question_answered: Is printed Conjecture 3 of arXiv:2606.16828v1 true? Only that printed assertion is targeted.
Plan: first attempt Mathlib instantiation and frozen projections with normalization. If this suffices, stop as bind-only without a module. Otherwise build the verified evaluator and refutation, proposed proof_shape=content, admission_basis=escape-witness, utility kind=certified-instance; basis=refutes.
Stop if the rendered source differs from the brief, or an author v2 corrects the assertion. A previously posted but explicitly unverified calculation is not grounds for stopping and is never a numerical input.
Independent calculations: (1) memoized recursive evaluation using conjugation; (2) construct the reachable DAG using direct column deletion, then bottom-up evaluation.
Direct frozen dependencies: to be determined by the ordered library review before implementation.
Provenance: no skill; one Codex implementation worker, no independent review agents. Independent algorithms are two implementations by this same worker, not independent human/model sources. Source and prior-post checks will be recorded separately.
