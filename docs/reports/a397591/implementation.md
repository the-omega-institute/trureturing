# A397591 implementation record

The first-tier task is the exact exponent-n OEIS NAME equation over integer
formal power series, with zero constant coefficient. The target is the `%C`
conjecture for every n > 3: odd coefficient iff n = 2^k - 1 or 2^k + 1,
with k > 1. The base is 588fe7fd3d5ebd6044a92be4bff1114968ade78b.

## Preregistered proof route

Proposed escape witnesses: the coefficientwise contracting normalized row
construction gives an integer solution without dividing in a finite field;
the reduction of 1-A modulo two is `(1+X)^2 U`, where U is the Catalan
series modulo two. The latter identity, proved from normalized rows and
uniqueness, is the proposed active intermediate for the support theorem.
These are unbounded symbolic obligations, not positive finite certificates.
The proposed normalization for row exponent n+1 is row minus derivative-row.

Stop as success only with the full target, `make lean` exit zero, standard
axioms only and an opened PR; refutation requires a kernel witness; blocked
requires a concrete Lean attempt and the sharp remaining goal. No theory
volume or atom is created. No finite probe is claimed as mathematical progress.

## Search receipts

- Repository search: `rg 'A397591|A397590' D5` has no hits at the pinned base.
- The complete SquareExponentDyadicSupport source was read as a route reference;
  its scaffolding is private, its exponent is squared, and its conclusion is a
  different support set. It will not be altered or referenced by private names.
- Public interfaces of CatalanCompositionSquareParity and the general
  convolution_pairing lemma are being inspected for direct reuse.
- `gh search code 'A397591 language:Lean' --json path,repository,url --limit 100`:
  exit 0, `[]`. Repository search `gh search repos A397591` also exits 0 with `[]`.
  HTTP-level receipts and third-party ecology checks follow separately.
- User-supplied literature evidence: valid arXiv all:A397591 query returned
  totalResults=0; OEIS marks Conjecture and supplies only its b-file. Those
  observations are user reports until independently fetched in this attempt.
  A397590 is a different object and supplies no transferable theorem here.

## Not claimed

No global absence-of-proof claim, no proof from the finite sample, no theorem
about A397590 or A397902, no completed Lean result, no independent review yet.
Pages not successfully opened in this attempt are ASSUMED-UNVERIFIED.

## Provenance

Codex implementation worker, using the lean4 skill with repository/user build
and persistence rules taking precedence. Single implementation source and
self-checks; no independent review or orchestrator recheck is asserted.
