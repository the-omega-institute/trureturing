/- GID: D5/X_Frontier/HeartsDraft
   generality: E
   mirror-B: none(waiver:human-gated-draft-in-result)
   mirror-E: none(waiver:no-experiment-before-statement-approval)
   anchors: []
   digest: Bind a closed O-6 draft to the concrete Weil zero sum; await the Hearts gate. -/

import D5.S3.Weil.WeilIdentity

/-- TASK D5-T0001 | 难度:5 | 依赖:就绪✓ | 尝试:3
    提示:Candidate B is frozen in D5/X_Frontier/Hearts with MeromorphicOn plus AnalyticAt zero localization and no pole-free-band clause.
    尸检:M0 draft parameterized arbitrary Zqc/Witt data and let a structuralSingularities set absorb every nonanalytic point; rejected as a dictionary statement rather than the independent engine. R2 first candidates also asserted a pole-free band, contradicted by the zeta(phi^3 s) structural pole in 6.19; that clause was removed. Cross-model adversarial review judged candidate B faithful and it was adopted; O-6 was separated because its draft left the Weil functional free. -/
def heartsDraftTicket : Unit := ()

/-- TASK D5-T0018 | 难度:5 | 依赖:欠(Hearts-gate) | 尝试:2
    提示:G is draft-ready, awaiting Hearts gate; A/B/C/D/E/F are bound in D5/S3/Weil and Hearts remains untouched.
    尸检:XM-1 rejected O6WeilPositivity with a free functional parameter as vacuous; repository and pinned mathlib inspection found no canonical Weil explicit-formula functional to bind in D5-T0001. -/
def o6WeilExplicitFormulaTicket : Unit := ()

/-
COMPLETED SUBTICKET D5-T0018-D: D5/S3/Weil/PrimePoleTerms binds the concrete
von Mangoldt prime sum, pole terms, and completed-zeta digamma integral with convergence data.

COMPLETED SUBTICKET D5-T0018-E: D5/S3/Weil/ZeroSum binds exact zeta-zero
multiplicities, classical zero symmetries, and the finite symmetric-cutoff limit.

COMPLETED SUBTICKET D5-T0018-F: D5/S3/Weil/WeilIdentity binds the prime,
pole, archimedean, and zero terms by the registered classical Weil identity,
with concrete ZeroData and convergence hypotheses and no positivity claim.

DRAFT-READY SUBTICKET D5-T0018-G, awaiting Hearts gate: the closed proposition
below states the non-vacuous O-6 nonnegativity claim on `convolutionSquare`.
-/

namespace D5.X_Frontier.HeartsDraft

open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum

/-!
## O-6 statement draft and RH relation

`o6WeilPositivityStatement` is closed: every value is bound by the proposition.
`Z` is not a free zero set or functional; `ZeroData` forces a duplicate-free,
exhaustive enumeration of the actual nontrivial zeros of `classicalZeta`, with
their exact analytic multiplicities, reflection/conjugation symmetries, and
finite symmetric cutoffs. `g` is the repository's even, smooth,
compactly-supported complex test function. `convolutionSquare g` is exactly
`g star g tilde`, where `g tilde (x) = conj (g (-x))`, and `hZero` is the exact
symmetric convergence witness required by `zeroSum`.

The conclusion uses the real part because the repository's concrete zero sum
is complex-valued. `WeilIdentity.weil_explicit_formula` identifies this same
zero sum, whenever the concrete archimedean convergence witness is supplied,
with `poleTerm - primeTerm + archimedeanTerm`; no Weil functional is a
parameter of this statement.

Classically, Weil's criterion says RH is equivalent to this nonnegativity for
every convolution square in the stated test class (with the standard
existence and convergence facts represented here by explicit inputs). This is
why O-6 is a heart and remains open: proving the future Hearts theorem,
together with the classical equivalence, proves RH. This draft neither assumes
RH nor declares the proposition proved.
-/

/--
The closed, non-vacuous O-6 proposition prepared for the protected Hearts
module. This is a `Prop` definition, not a theorem or an axiom.
-/
def o6WeilPositivityStatement : Prop :=
  ∀ (Z : ZeroData) (g : WeilTestFunction)
      (hZero : SymmetricConvergent Z (convolutionSquare g)),
    0 ≤ (zeroSum Z (convolutionSquare g) hZero).re

/-!
## Independent three-view audit

1. Faithfulness view. Weil's 1952 positivity criterion uses even smooth compact tests, the
   involution `conj (g (-x))`, convolution squares, the multiplicity-weighted
   nontrivial-zeta-zero sum, and nonnegativity. The definition above maps these
   respectively to `WeilTestFunction`, `involution`, `convolutionSquare`,
   `zeroSum`, and `0 <= ... .re`. The F-level explicit formula binds that zero
   side to the concrete prime, pole, and archimedean side.

2. Non-vacuity view. The rejected XM-1 functional parameter is absent. Every
   quantified input is concrete and used: `Z` fixes the actual zeta zeros,
   `g` fixes the test and its square, and `hZero` supplies exactly the limit
   consumed by `zeroSum`. There are no declaration parameters or unbound
   variables. Formal construction of a `ZeroData` value and general
   convergence remain explicit analytic prerequisites rather than hidden
   axioms; this is the A-F interface requested by D5-T0018.

3. No-RH-theft view. `ZeroData.gamma` is complex and its reconstruction is an
   identity valid without RH; no field says `gamma.re = gamma` or
   `rho.re = 1 / 2`. The draft is only a `Prop` definition, has no proof body,
   and introduces neither `sorryAx` nor an axiom. Only the future protected
   theorem below uses the intentional `sorry`, so the open claim is not
   smuggled in as a proved result.

Audit verdict: faithful, concretely bound, and still open. This is a
single-worker three-pass audit, not an independent multi-model consensus.

## Digestion Ledger

`Meta/BACKFILL.yaml` already records the digestion coverage for
`D5/X_Frontier/HeartsDraft`. The applicable entries truthfully remain
`migration: partial` / `truth: open`: a compiled statement draft is neither a
proof receipt nor an absorbed theorem. Therefore this draft causes no
Digestion Ledger byte change. After an authorized monument, add
`D5/X_Frontier/Hearts` to those two `coverage_gids` lists, but keep the truth
state open while the Hearts proof is `sorry`.

## Monument checklist

The current protected source anchor is Git blob
`d9b272d7eff465351f4871cda8ea93ec50a6765f` and file SHA-256
`ebf0679b7fe56d7d09bae569c348a4dc43a93df5bde9e657db9590ec7238c663`.
The current `Meta/BACKFILL.yaml` Git blob is
`629b78e622fa57c0c9c603da6fbfdf84fc8f4cfe`. Do not apply the patch on
different source blobs.

Current SL-008 semantics compare the entire canonical Hearts declaration
report with the baseline. Adding O-6 therefore returns
`semantic declaration identities and types are frozen` and is a hard block.
`ledger-reattest` cannot authorize it: reattestation preserves statement
identity and rejects semantic changes. Before applying this patch, the Hearts
gate must land a typed, exact-statement approval mechanism (or an equivalent
new baseline epoch) that permits this append while continuing to freeze every
existing Hearts declaration. Because that mechanism changes the harness, it
must itself pass SL-022 protected-surface review and the conservative replay
gate. A plain Reattest event, admin bypass, or direct baseline substitution is
not approval.

After that prerequisite gate is active, execute from a clean branch based on
the approved `origin/dev`:

1. Verify the pinned source blobs, extract the patch below, and run
   `git apply --check --unidiff-zero -`; then repeat the pipeline with
   `git apply --unidiff-zero -`. The same patch adds
   `D5/X_Frontier/Hearts` to the applicable coverage lists while
   retaining `partial/open`.
2. Run `lake build`, candidate and baseline Lean inspection, and the axiom
   audit. The only new open declaration may be
   `D5.X_Frontier.Hearts.o6_weil_positivity` with `sorryAx`; there must be no
   new unregistered axiom.
3. Commit the content so all attested blobs are Git-reachable. Generate the
   candidate report with `Meta/StrataLint/lean-inspector/inspect.sh`, then run
   the repository CLI exactly as shown below. It must report no semantic
   identity change. Commit any generated Reattest events separately; if it
   rejects the O-6 statement, the prerequisite Hearts gate is not active.
4. Run `make dotnet test` and `make gate BASE=origin/dev`. Require rc=0 and
   the repository's required checks. The monument PR needs the recorded Hearts
   authorization plus independent statement review; do not push/merge by
   bypassing SL-008 or SL-022.

Patch extraction/check command (repeat with `git apply --unidiff-zero -` only
after the gate is active):

test "$(git hash-object D5/X_Frontier/Hearts.lean)" = \
  5b0fd40cdd70377b514014625955f11d74f1fd33
test "$(git hash-object Meta/BACKFILL.yaml)" = \
  629b78e622fa57c0c9c603da6fbfdf84fc8f4cfe
sed -n '/^diff --git a\/D5\/X_Frontier\/Hearts.lean/,/^"#$/p' \
  D5/X_Frontier/HeartsDraft.lean | sed '$d' | \
  git apply --check --unidiff-zero -

Meta/StrataLint/lean-inspector/inspect.sh --repository "$PWD" \
  --output .lake/build/stratalint/raw-lean-report.json
dotnet run --project Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj \
  --configuration Release -- ledger-reattest --candidate-lean-report \
  .lake/build/stratalint/raw-lean-report.json

-/

/-- The exact, source-pinned Hearts patch; data only, never applied by this draft. -/
def o6MonumentPatch : String :=
  r#"
diff --git a/D5/X_Frontier/Hearts.lean b/D5/X_Frontier/Hearts.lean
--- a/D5/X_Frontier/Hearts.lean
+++ b/D5/X_Frontier/Hearts.lean
@@ -6 +6 @@
-   digest: Freeze O-5 zero localization; defer O-6 until D5-T0018 binds the Weil functional. -/
+   digest: Freeze O-5 zero localization and the classical O-6 Weil positivity statement. -/
@@ -7,0 +8 @@
+import D5.S3.Weil.WeilIdentity
@@ -15,0 +17,2 @@
+open D5.S3.Weil.TestFunctions
+open D5.S3.Weil.ZeroSum
@@ -22,8 +25,7 @@
-O-6 is deliberately not declared in this file. The classical Weil criterion
-(Weil 1952) states its future theorem as nonnegativity of the explicit-formula
-functional on convolution squares of even, smooth, compactly supported test
-functions. Neither this repository nor pinned mathlib currently defines that
-functional, including its prime, pole, zero, and archimedean terms. Treating
-the functional as a free parameter would make the purported heart vacuous.
-D5-T0018 records the exact binding obligation before an O-6 declaration may
-be added.
+O-6 is the classical positivity heart associated with Weil's 1952 criterion.
+D5-T0018 binds its
+test class, involution, convolution square, multiplicity-aware zero sum, and
+symmetric convergence convention to concrete definitions. Its unresolved
+proof body is intentional. Classically this positivity for every convolution
+square is equivalent to RH, so proving it would prove RH; the `sorry` records
+that open boundary rather than assuming RH or claiming a proof.
@@ -72,0 +75,11 @@
+/--
+O-6 (positivity): the concrete multiplicity-aware zeta-zero sum is
+nonnegative on every convolution square of an even smooth compactly supported
+test. `Z`, `g`, and the symmetric convergence witness are all bound; no Weil
+functional is a free parameter.
+-/
+theorem o6_weil_positivity :
+    ∀ (Z : ZeroData) (g : WeilTestFunction)
+        (hZero : SymmetricConvergent Z (convolutionSquare g)),
+      0 ≤ (zeroSum Z (convolutionSquare g) hZero).re := by
+  sorry
diff --git a/Meta/BACKFILL.yaml b/Meta/BACKFILL.yaml
--- a/Meta/BACKFILL.yaml
+++ b/Meta/BACKFILL.yaml
@@ -355,0 +356 @@
+          - D5/X_Frontier/Hearts
@@ -393,0 +395 @@
+          - D5/X_Frontier/Hearts
"#

end D5.X_Frontier.HeartsDraft
