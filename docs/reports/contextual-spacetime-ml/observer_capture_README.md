# Interval capture after a precision switch

`observer_capture.py` consumes the delivered `rational_observer` construction,
certificate verifier and ties-down rounding for
[observation companion §44](../../develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML_OBSERVATION.md).
Python 3.10 or later and its standard library suffice. From the repository root:

```sh
python3 -B docs/reports/contextual-spacetime-ml/observer_capture.py checks --out docs/reports/contextual-spacetime-ml/observer_capture_results.json
printf '0010110100\n' | python3 -B docs/reports/contextual-spacetime-ml/observer_capture.py stream --old-label 23 --reports 10
```

Paths may instead be absolute; imports resolve beside the script. `--out` is an
explicit destination, relative to the invoking directory if relative. The
stream defaults are `--p 1/4 --r 1/4 --eps 1/16 --target 1/1024`. Omitting
`--old-label` starts at the ordinary initial label for the empty history.
Supplying it requires actual membership in that old label's interval. Integer
range validation cannot prove that precondition. The example's old label 23
is obtained after history `00` or `0100` in the old `m=28` observer.

`TwoTrackCapture(p, r, eps, old_label=None)` starts in Ready.
`request(eps, reports=None)` prepares and verifies the target table and a
positive inward margin, checks matching model parameters, and chooses or
validates a report threshold. It then seeds the target at the nearest center
with lower ties. Requests during Warm are rejected without changing the state.
Preparation assumes the report source can wait; it processes no hidden reports.
The object accepts new requests after each completed capture, including looser
tolerances. It retains no history archive, exact posterior, or pre-switch clock.

`step(0)` and `step(1)` update both labels during Warm. `readout()` returns the
active index, its tolerance and its exact next-zero prediction as decimal
numerator/positive-denominator string pairs. During Warm it also returns the
target index and tolerance, counter and threshold. Counters range from zero to
`T-1`; the `T`th report switches directly to Ready with the updated new label.
All earlier outputs use the updated old label. Thus the old tolerance remains
valid throughout warmup, and the new tolerance and interval membership hold
at handoff. Choosing a looser target does not preserve all former tighter
guarantees. These claims are conditional on the initial membership precondition.

The stream command prints the initial Warm output and one line after each
report. ASCII whitespace is ignored. EOF without further reports leaves the
counter unchanged; elapsed time supplies no completion guarantee. Invalid
reports, parameters, labels and thresholds produce explicit errors and nonzero
exits. A failed preparation leaves the current Ready state intact.

The sufficient bound is `eta^T E / 4 <= mu`, with `T >= 1`. Here
`E = k_old + eta/(2 m_new r(1-r))` and
`mu = min(r k_new eta/(4 K_new^2), eta p r/(1-p-(1-2p)r))`.
`threshold_holds` checks the cross-multiplied integer inequality, including
equality. `sufficient_reports` searches that inequality; it does not find the
minimum actual capture time. `bernoulli_reports` gives the alternative rational
upper bound in §44.5. For the concrete switch, `E=793/1578`, `mu=4/16641`,
ten reports satisfy the inequality, and the looser Bernoulli choice is 522.

`verify_margin(certificate, margin)` calls the existing ordinary verifier, then
tests `4N` supplied-margin successor endpoint inequalities. It rejects
nonpositive margins and accepts arbitrary ordinary certificates satisfying
these inequalities, without constructor equality. The experiments include a
non-grid one-state certificate, a smaller valid margin and an excessive margin.
The controller itself always uses the delivered grid constructor; the generic
margin check alone does not establish the grid reset formula for arbitrary
certificate layouts. The private pair helper is restricted to constructed grids.

The retained exact results contain:

- Five rational grids with `m=28,526,2,16,10`, both clipped sides, saturated
  `k=1`, and both report transitions. An independent `Fraction` calculation
  weights two hidden masses before mixing them, then checks every strict
  successor endpoint. The reference is parameterized by `p,r`.
- All 29 resets checked against an independent full-grid nearest-point scan.
  The ties are `7 -> 131`, `21 -> 394`. New midpoint transitions are
  `T0(263)=394`, `T1(263)=131`; their sum is 525, so rounded reflection is not
  assumed.
- Exactly `29 × 1024 × 2 = 59,392` terminal endpoint comparisons, covering
  every old interval, every ten-report word and both endpoints. Shared tree
  prefixes reduce repeated computation without removing any terminal cases.
  The minimum observed membership slack is `22193627/19687023122`, attained
  by the retained endpoint/word witness. This is a finite experiment, not the
  all-history proof or a minimum-delay claim.
- A repeated `1/16 -> 1/1024 -> 1/16 -> 1/128 -> 1/32` trace with warmup
  lengths `10,1,7,3`. Both updated labels, the proof-only exact reference,
  pre-handoff old outputs (including counter zero), handoff membership,
  no-report stasis, request refusal and subsequent Ready updates are checked.
- Threshold equality and failure, `T>=1`, positive margins, malformed ordinary
  certificates, mismatched parameters, invalid labels/reports and failed
  preparation. Expected rejections are named in the results.
- Separate logical examples: legal posterior `000` with alternative label 449
  has error `13/14728 < 1/1024` but exceeds that interval's upper endpoint by
  `31/473788`. It is not a switching execution trace. Histories `00,0100`
  share old label 23, giving the old-label-only lower bound `1/456`, while their
  canonical fine labels are 438 and 429 and their common reset is 432.

The paper proof applies Quantum §153's common-report logit contraction to the
actual filter and an exact reference initialized at the new center. ML §41's
interval invariant absorbs the reference-to-grid rounding; the rounded machine
is not claimed to contract. Strict inward margin then gives finite membership,
which supports repeated requests. ML §§21.2/39.7 and RRO §§2.2–2.3/4.1 supply
the initial-error, initialization and observation distinctions. These are
repository-derived arguments with no Lean certification or novelty claim.

A fixed finite menu has the finite Ready/Warm carrier in §44.10; arbitrary
rational targets give only a stagewise-finite algorithm. Both labels, counter,
mode and machine identifiers cost memory. Tables and certificates, construction,
validation, reset arithmetic, growing threshold integers, both updates, access,
output and scratch are additional costs. Python objects and JSON are not an
implementation of the abstract bit counts. A live source that cannot wait needs
separately charged buffering/concurrency; no wall-clock real-time claim is made.

The existing eight-report `observer_switch.py` contract and retained results
remain a separate output-accuracy experiment. Its campaign is not repeated here.
Successful checks write `valid: true`; unexpected failures exit nonzero before
writing a new results file. A previously existing results file is not a receipt
for a failed run.
