# Two-model finite observer

model_selector.py implements observation-companion §50 for one globally fixed
unknown p in {1/4, 1/3}, known r=1/4, and the fair initial hidden-bit prior.
The old bit emits, then flips. After consuming report 2M, the output predicts
report 2M+1. For each fixed true model, the mathematical guarantee is probability
at least 1−delta of error at most epsilon at **every** time n ≥ 2M.
This concerns the next-zero conditional probability given the complete observed
word, not the realized next bit or the whole joint record law.

Run from the repository root with Python 3 (standard library only):

    python3 docs/reports/contextual-spacetime-ml/model_selector.py checks \
      --output docs/reports/contextual-spacetime-ml/model_selector_results.json
    printf '011001\n' | python3 docs/reports/contextual-spacetime-ml/model_selector.py \
      stream --epsilon 1/64 --delta 1/2

The stream consumes one byte at a time, accepts ASCII bits and ASCII whitespace,
and emits one JSON line for the empty history and after each report update.
Each line has model, label, and the exact two-string prediction pair.
Before selection, model and label are null and prediction is ["1","2"];
there is no epsilon promise in that phase. The stream keeps no report history.
Delta=1/2 needs 3,318 reports, so the short example remains in training.

The Python constructor is ModelSelector(epsilon, delta). Each parameter must
be exactly the imported Q type or a list of two canonical decimal strings
[numerator, positive_denominator]. Epsilon must be positive; delta must be
strictly between zero and one. Integers, booleans, floats, Fraction, strings,
tuples and arbitrary objects are rejected at this boundary. CLI rational text
uses the owner's cli_rational; no float parsing is introduced. Unreduced pairs
are allowed. Their mathematical equality must be checked by cross multiplication
or both order comparisons, not Q's stored-pair dataclass equality.

step(report) accepts only type(report) is int and report in (0,1), and returns
the updated readout. Invalid reports fail before any state changes. Input/domain
errors raise CertificateError; command failures return a nonzero exit code.
The private _diagnostic entry is solely for small-M experiments on already
verified tables: its delta and L are null and it offers no production delta
guarantee. The production constructor and CLI have no M override.

Production imports Q, rational, cli_rational, CertificateError, construct,
verify, emit and require from rational_observer.py. Both constructed
certificates must pass the actual verifier. They remain ordinary
rational-observer-interval-v1 objects, with separate states tables and
target positions 0 then 1. No product transition table or new certificate schema
is created. The label step is states[j]["targets"][report]; production never
uses the reference posterior update or IntegerObserver.

During training the dynamic tuple is (k,c,pending,label_A,label_B): completed
pairs 0 ≤ k < M, matches 0 ≤ c ≤ k, and pending equal to None, 0 or 1.
Both labels process every report from their fair-prior initial states. The final
second report updates both labels, finishes the count, chooses the model, saves
its updated label, and sets the entire training tuple to **None before the
first selected readout**. Thereafter only model identity and its label depend on
history. There is no continuing clock, counter, unselected label, stored word,
or exact posterior. Parameters, L, M and the two certificates remain fixed.
Callers must not mutate the machine fields or certificate tables.

For delta=a/b, repeated integer doubling computes the least L with
2^L a ≥ b, then M=(41472L+24)//25. The classification threshold is
288c ≥ 157M, with equality assigned to A. Disjoint-pair *match indicators*
are iid separately under each fixed model, with means 9/16 and 19/36.
The raw report pairs need not be independent. Classifier prior invariance does
not extend the fair-prior prediction theorem; mixing a random global model
does not supply unconditional iid indicators.

The compact controller's nominal report-boundary state bound is
3M(M+1)N_A N_B/2 + N_A + N_B. This is not a reachable-state count, minimum,
or instruction microconfiguration count. The larger
2(2M+1)(M+1)N_A N_B + N_A + N_B describes a different redundant encoding.
Training fields cost O(log(M+1)+log(N_A)+log(N_B)) dynamic bits plus constant
mode/pending identity; after selection one tag and one label remain.

Costs use main-volume §41.6's binary record/access model, not Python object
sizes or timings. For generated record widths b_A,b_B including parameter and
index encoding, static tables/certificates use O(N_A b_A + N_B b_B) bits and
construction and complete verification each use O(N_A b_A² + N_B b_B²) bit work.
Both accepted certificates require 11(N_A+N_B)+4 scalar inequalities, plus
structural and parameter validation. Encoded inputs and O(log(M+1)) controller
constants are charged separately. With charged random access, all **2M**
training reports each cost O(b_A+b_B+log(M+1)), including the final threshold;
each later report costs O(b_selected). Serial storage pays full table scans.

For delta's positive integer-pair encoding, §50 declares unary length prefixes,
one delimiter per integer and binary payloads, of total
D=2 bit_length(a)+2 bit_length(b)+2. Thus L≤D; initialization uses
O((L+1)D) bit work and O(D) scratch, followed by constant-integer
multiplication/division for M. D is not JSON byte length. Scratch, output,
input/parameter storage and static tables are separate from persistent labels.
The static unselected table may remain after its dynamic label is deleted.

The checks generate the adjacent results file deterministically:

- For both models, priors 0, 1/2 and 1, and 1–3 disjoint pairs, enumerate all
  504 report words across 18 cases. Aggregate all 84 full match-vector
  probabilities and compare them exactly to Bernoulli product probabilities.
  Compare classifier tails to independently summed exact binomial tails.
- Check threshold equality and neighboring counts at M=288, c=156,157,158;
  nine dyadic fenceposts, including delta=1/1000 giving (L,M)=(10,16589)
  and delta=2^-100 giving (100,165888); also check unreduced delta=2/4.
- At epsilon=1/64, actually construct and verify 47 and 37 states, with
  519 and 409 scalar comparisons. The verifier's supplied-integer maxima,
  30 and 27 bits, are not complete record widths.
- For diagnostic M=1,2,3, all training words and all suffixes of lengths 0–3
  yield 1,260 correctly selected readout comparisons, including the selection
  boundary, against independent two-component Fraction hidden masses.
  The mass recursion is imported from observer_capture.mass_step, with
  explicit initial masses for the different classifier priors.
- On true A, diagnostic M=1, prefix 11, the next-zero target is 5/12:
  fresh error 1/552 is within 1/64; stale error 5/276 and reset error 1/12
  exceed it. Cleanup is checked inside the first selected readout, and
  remains checked on subsequent transitions.
- Reject 58 invalid parameter calls, 8 invalid count calls and 24 invalid
  report calls. A linear production run consumes all 3,318 training reports
  and 12 later reports. An incremental source and discarding sink check
  the initial output and three update outputs without collecting history.

These finite experiments do not prove infinite iid or all-future accuracy.
The latter uses the §41 all-word invariant on the single correct-classification
event, with no time union bound. Incorrectly selected paths are not required to
violate epsilon. No enormous production word space is enumerated.

The checks and CLI were also exercised with CPython 3.9.6 on macOS, from a
different working directory and a copied source directory containing spaces,
without loading shell startup files. The results were byte-identical. Other
platforms were not exercised by this implementation seat.

Mathematical ownership: Quantum §153 supplies model convention, timing and
positive word mass; main ML §§41.1–41.6 supply the known-model machine, invariant,
certificate and costs; §§34.5–34.6 supply the fixed global model distinction.
Observation §48 is the same-family all-word obstruction. §49 concerns a
different known static-mixture problem. RRO supplies interpretation of approximate
observations versus exact fibre quotients, not extra premises or certification.
Known-p small-r/overlap bounds do not establish optimality here, and coarse
epsilon can make identification unnecessary.

Concentration is reused from Hoeffding, *Probability Inequalities for Sums of
Bounded Random Variables*, JASA 58(301), 13–30 (1963),
DOI 10.1080/01621459.1963.10500830; metadata was checked against Crossref.
Pinned mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d has
Mathlib/Probability/Moments/SubGaussian.lean SHA-256
7259bc145c6de9bb81b8aea24a660b951f12787ffdb7514ba27de74fb658e151.
ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc gives parameter 1/4 for a
centered measurable variable supported on an interval of length one, under a
probability measure. Apply it to -C for A's lower tail and C for B's upper tail.
ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
applies to those independent centered sequences with nonnegative threshold
M·5/288; its exponent is −25M/41472. Each fixed model uses one side,
without a factor two. The pinned source was inspected, not composed or compiled
in Lean. No Lean wrapper, concentration theorem or novelty claim is added.

Source basis: repository commit f59a9fa2130589e591661194c72074ea8d10538a;
the unchanged imported owners have SHA-256
82df94f295dfddbd676a73d226a64b444b85d375cf7ed7f988e677d27787e313
(rational_observer.py) and
e63d2db9e67fb24ed6713b7b4ab8917afa2c02237b650a478395bdf43890984b
(observer_capture.py). The mathematical composition is repo-derived; Hoeffding
is literature-attested. Producer: AI, Codex (GPT-6), implementation seat
ml-identification-implementation-0917, 2026-09-17; skill:
theory-volume-template. Program and scoped checks are from this same seat.
Independent review, canonical full preflight, Lean validation and CI are not
claimed by these experiment results.
