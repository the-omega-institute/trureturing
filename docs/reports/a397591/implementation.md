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

## Retrieved source and numeric probe

- https://oeis.org/search?q=id:A397591&fmt=json: HTTP 200, 3042 bytes, SHA-256 `e30a5609590bf9e3b9ed4d8bcf4a96235bbd318d1ae1eec4cef4f9c245c2dca5`
- https://oeis.org/A397591/internal: HTTP 200, 14833 bytes, SHA-256 `2fc5cf2d5ed7780ff68a6c09aad0167565f9594cdaadec60d167df3ba59688ff`
- https://export.arxiv.org/api/query?search_query=all:A397591: HTTP 200, 696 bytes, SHA-256 `049d997b380972359655e5e76f3b8b3bc117cbc8ebe1949cbd28b166f4537852`
- https://reservoir.lean-lang.org/: HTTP 200, 115518 bytes, SHA-256 `cc504927f480af574c3fad96053941a720162b6b4b23ff5452e3def7eae9777b`
- https://api.github.com/search/code?q=A397591+language%3ALean: HTTP 200, 55 bytes, SHA-256 `4af480b8ee5b87b369a76c49bd22c9a783908272ebffbe97898f8ab0f0772a5f`, total_count=0
- https://api.github.com/search/repositories?q=A397591: HTTP 200, 55 bytes, SHA-256 `4af480b8ee5b87b369a76c49bd22c9a783908272ebffbe97898f8ab0f0772a5f`, total_count=0

The parsed OEIS response confirms the exact NAME, conjecture, offset 1, and
only one link (the 400-term b-file). The arXiv Atom feed has totalResults=0.
Reservoir homepage is a successful availability check, not a negative search.
Global GitHub code search covers indexed Lean repositories; unindexed projects
are outside this bounded search. Pinned Mathlib PowerSeries Derivative/Expand/
Catalan and repository CatalanCompositionSquareParity were inspected.
The public binary_catalan theorem is directly reusable and will be imported.
convolution_pairing is general, but the proof here uses Mathlib Frobenius
coefficient extraction rather than an Icc convolution sum.

N=120 exact-integer rerun: all 7260 coefficient divisions and 120 row
divisions were exact; the first 21 coefficients match OEIS DATA individually.
The odd indices in 4..120 are 5,7,9,15,17,31,33,63,65; 108 terms are even.
The target predicate has zero counterexamples and the deliberately wrong
power-of-two predicate has 14. All supplied probe readings match.

Cache preparation: make lean-cache-ensure exited 0, status=seeded,
method=clonefile, clonefile_attempts=1, project and Mathlib both warm,
stamp_miss=null. Donor /Users/chronoai/trureturing.

## Kernel-checked construction

The exponent-n scaffold compiles with `lake env lean` after the recorded cache
ensure (exit 0). It proves exact normalization, coefficientwise contraction,
stabilization, and integer existence and uniqueness for the exact NAME equation.
The normalization is `R-T`, using `(n+1)-n=1`; this is a new exponent-n
construction, parallel to the private square-exponent construction. No parity
classification is claimed at this checkpoint. Compiler output contains only
unused-simp-argument warnings, scheduled for cleanup before the full gate.

The exact modulo-two identification now compiles without warnings (file-level
Lean exit 0). The decisive diagonal statement is
`coeff m (candidate^m*(1+X*U))=0` for every m>0. Odd m gives a square in an
odd degree; even m halves by U=1+X*U² and U*(1+X*U)=1. This makes the even
normalized rows vanish. The odd rows vanish from EO=candidate. Normalized
uniqueness then proves the proposed modulo-two identity. One algebraic repair
was needed: the even/odd split of (1+X)U consumes (1+X) times U's equation,
not the unmultiplied equation. The full support classification is next.

The full source-domain theorem now compiles without warnings (file-level Lean
exit 0): for arbitrary integer A satisfying DefiningEquation and every n>3,
Odd(coeff n A) iff n=2^k-1 or n=2^k+1 for some k>1. Its support step directly
uses frozen binary_catalan. The two shifted Catalan supports cannot overlap
above degree three: both corresponding powers would be divisible by four
while differing by two. This explains the source's strict n>3 cutoff.
Full project, report, Scribe and deposit gates remain to be run.

## Full build and placement

`make lean` exited 0 in 237.854 seconds on this macOS ARM worktree, with
12958 jobs. The build's LEAN_CACHE receipt is status=present, method=none,
stamp_miss=null, project_olean_state=warm, mathlib_olean_state=warm. The prior
ensure receipt records clonefile seeding; no cold bare Lake command was run.
The log is runner-owned `make-lean.log`; its final sentinel is
`MAKE_LEAN_EXIT=0 BUILD_SECONDS=237.854`.

The route command confirms the canonical address
D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport. New LinearRows
subdirectories started empty; the existing Parity mirror had 58 recursive
files and was not selected. Library/notes had 27 direct files before this
note. The source and mirror fit the registered S1 Recurrence domain. The
manifest's artifact is `lean` (an initial empty-artifact invocation was rejected
without mutation, then corrected). The seven-line header follows spec A5.1.
