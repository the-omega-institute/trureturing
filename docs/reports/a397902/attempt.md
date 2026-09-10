# A397902 implementation attempt

Origin: Codex implementation worker, using the local `lean4` skill. Single worker;
no independent review or multi-model consensus is claimed. User supplied the
literature adjudication and probe expectations; measurements below were run here.
Base: `0011b3f0dfdd9eb32b753d122219f0749927922a`, branch `lane/math/a397902`.
Tier: 第一档. Target: all n > 2, for the zero-constant integer formal series in
the OEIS NAME. Rational construction does not discharge integer existence.

## Numerical probe (not a theorem or mathematical progress)

The exact recurrence from the task was run in Python arbitrary-precision integers,
N=90. Both divisions were asserted before taking each quotient. Results:
4095 successful j-divisions; 90 successful e-divisions; first 16 coefficients
match the live OEIS DATA individually; 0 conjecture mismatches for n=3..90;
70 even coefficients. Actual odd indices:
`3,4,5,6,7,8,13,14,15,16,29,30,31,32,61,62,63,64`.
Negative control: explicitly use the wrong predicate `False`; 18 mismatches.
The user's wrong predicate was unspecified, so equality is of mismatch counts,
not a claim that the two negative-control predicates were identical.
Measured recurrence runtime: 0.034471667 s on this worktree host.

OEIS request: https://oeis.org/search?q=id:A397902&fmt=text
HTTP 200, 2734 bytes, SHA-256
`eac596ae2bcf450245d98d5bb3ef4106b4ce2945b721165bee45dfab40bdc9c5`.
Read NAME, Conjecture, DATA, formulas, author and cross-references directly.
The fetched text labels the parity assertion Conjecture and links only the b-file.
Asymptotics do not assert parity. No conclusion is transferred from A397591,
A397596, A397594 or A397592.
Raw response and probe output are in the runner attempt directory.

## Search and proof status

D5 exact text search for A397902, A397594, A397592, A397591, A397596: no matches
(`rg`, exit 1). Pinned mathlib: v4.33.0,
`db584cd6d46c92f209a44c0f1c829460d327499d`.
Further library searches and Lean proof work are pending.

## Not claimed

No all-n theorem, integer existence proof, counterexample, freeze, coverage,
build success or PR is claimed at this checkpoint. The numerical probe is only
an instrument check. User-reported arXiv evidence has not yet been re-fetched;
its origin remains user input, not a worker measurement.

## Library search receipts and revised proposed witness (before Lean implementation)

- GitHub REST code search `A397902 language:Lean`: HTTP 200, 55 bytes,
  SHA-256 `4af480b8ee5b87b369a76c49bd22c9a783908272ebffbe97898f8ab0f0772a5f`,
  `total_count=0`, `incomplete_results=false`. Scope: publicly indexed Lean code,
  including third-party Lean repositories; not a proof of global absence.
  URL: https://api.github.com/search/code?q=A397902%20language%3ALean
- arXiv: https://export.arxiv.org/api/query?search_query=all%3AA397902&start=0&max_results=10
  HTTP 200, 696 bytes,
  SHA-256 `5006f81abc74c9b9ee0a11793c492485b9a51f391eaab596deacb3f45af57dfa`,
  valid Atom response with `totalResults=0`. This independently reproduces the
  user's bounded literature adjudication. Together with OEIS: open in this scope.
- Reservoir: https://reservoir.lean-lang.org/packages?q=A397902
  HTTP 200, 128624 bytes,
  SHA-256 `e38e8ce7de151a0f01e6f414174f282c21feb4ce08ee5022482ac9594e0f81cc`.
  INVALID QUERY for negative evidence: returned HTML does not echo A397902;
  generic hidden 'No results found' is not a query-specific result.
- Read the pinned `PowerSeries.coeff_pow` full statement and proof at
  `Mathlib/RingTheory/PowerSeries/Basic.lean:635`: finsupp-antidiagonal expansion,
  not normalized parity. Read `Derivative.lean` including `coeff_derivative`
  and `derivative_pow`: these supply the derivative identity needed below.
- Read all public declarations of `ConvolutionRecurrenceOddPowersOfTwo`,
  `DiagonalPowerRatioAllOdd`, and `PrimitiveEulerLedger` (and their defining
  predicates). The first exports a general `convolution_pairing`; the second
  exports `central_binom_even`, plus sequence-specific construction/uniqueness;
  the third exports integer Euler-product representation for any unit series.
  None states normalized square-exponent rows. Private helpers are not exports.
  Also screened prime-exponent and dyadic-row modules; their public conclusions
  do not identify this square-exponent sequence.

Proposed witness v2: replace explicit 2-adic precision bookkeeping by an exact
integer derivative normalization. This is a proposed proof route, not an assumption
or a proved statement. For positive k, e=(k+1)^2, g=(1-eX)^(-1), let
R=[X^k]F^e g and T=[X^(k-1)](F^(e-1) F' g + F^e g^2).
The product derivative gives k R=e T. The explicit Bezout identity
`e-k(k+2)=1` then gives `R=e (R-(k+2)T)`.
The normalized residual `R-(k+2)T` has new-coefficient multiplier 1.
This can construct the series over Z without assuming integrality and retains
exactly the division information before mapping to ZMod 2.

Possible binary candidate: write F=E(X^2)+X O(X^2), seek
`E+X O=1+X` and `E O=F`. These imply the normalized odd rows vanish;
the even rows reduce to a coefficient of a power whose 2-adic exponent exceeds
that of the degree. This coupled identity and its support classification still
need proofs. Proposed content witness: the live normalization/candidate-row
vanishing argument, not `coeff_pow` alone. No admission claimed yet.

Cache preheat succeeded: `make lean-cache-ensure` EXIT=0;
LEAN_CACHE status=seeded, method=clonefile, clonefile_attempts=1,
project_olean_state=warm, mathlib_olean_state=warm, stamp_miss=null.
