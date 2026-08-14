# Diagnostic Month R5 Lane B: Hidden Motion Dichotomy Open Report

Outcome: `open`, with no formalization deposit or cover. The synchronized
repository proves several strong component facts: arbitrary continuous paths in
the prime-adic hidden fiber are constant, continuous additive real hidden flows
are zero, one canonical integer jump is nonzero and has no continuous additive
real extension, the universal solenoid is connected, and its path-reachable
points are exactly one real-flow orbit. A checked candidate also proved that the
universal solenoid is not path connected.

Those facts do not prove the source's exhaustive dichotomy. The repository has
no source-faithful carrier for an arbitrary "hidden fiber change", no predicates
classifying such a change as a discrete prime-address jump or as accompanied by
a global solenoid phase path, and no theorem universally mapping every hidden
change into either branch. Conjoining component theorems and examples is
strictly weaker than a universally quantified disjunction.

No Lean, Blueprint, Scribe, Evidence, receipt, coverage, or frozen-ledger
artifact was deposited. The rejected untracked candidate files were removed,
and this report is the only intended repository change.

## Environment and synchronized baseline

The assigned isolated lane is:

```text
worktree = /Users/mstudio3/trureturing-diag-month-r4-b
branch = harness/diag-month-r5-b
```

The lane was initially synchronized from `4436226a` to
`67ec84c9ca8b9a1132d7445bc7efea4d26ba7a9a` with:

```sh
git merge --ff-only origin/dev
```

Exit `0`. After the first refreshed Lean report, `origin/dev` advanced by four
commits. `git diff --name-status HEAD..origin/dev` showed only these incoming
paths:

```text
A Blueprint/D5/S3/Weil/ZetaBridge/ConvolutionSquareOrbitBounds.md
A Blueprint/D5/S3/Weil/ZetaBridge/ConvolutionSquareOrbitBounds.scribe.cs
A D5/S3/Weil/ZetaBridge/ConvolutionSquareOrbitBounds.lean
```

The same fast-forward command was run again and exited `0`. The final pre-report
state was:

```text
HEAD       = a6dcb9be36dc5b929e4b96fe5310df95d78f3c75
origin/dev = a6dcb9be36dc5b929e4b96fe5310df95d78f3c75
ahead gap  = 0
```

`git merge-base --is-ancestor origin/dev HEAD` exited `0`, and
`git status --short` was empty before this report was added.

The live PATH declaration was read from
`tools/scripts/local-harness-gate.sh` and applied. `make help` exited `0` and was
read as the canonical command catalogue. On the final base, `make dotnet`
exited `0`, building all Release projects with zero warnings and zero errors.

The first `make lean-report` ran on the superseded `67ec84c9` base and exited
`0`; its report SHA-256 was
`5fa789a1e276bb8a06d8be5e69449dd409aa326da2ae109ef1d20342747a155d`.
It was not used as final evidence after the base advanced. The command was
rerun on `a6dcb9be` and exited `0` with:

```text
input_address = sha256:6474af698ff2fa87cb059baf4a2a35a929d556952ffbed0d6fb096416de98533
report_sha256 = 27c2df1bdb3b1eb95f235f24200744221818f4a338bd1ebf648eb76d3f87ba34
mode = produced
source_side = candidate
```

## Atom and authoritative statement

- Atom ID:
  `pzg-residual-85ace51c6a4dd01566ad4ee14028fc48bba25db190a01a8d09917eb4d6262f52`
- Source ID: `pzg-v170`
- Source path: `docs/develop/theory/PZG_BEDC.md`
- AST path: `corollary/20.4`
- Atomizer: `pzg-v1`
- Claim class: exhaustive hidden-change dichotomy plus hidden-motion rigidity
  and solenoid topology/path-component consequences.

The authoritative command was:

```sh
make show-atom \
  ATOM_ID=pzg-residual-85ace51c6a4dd01566ad4ee14028fc48bba25db190a01a8d09917eb4d6262f52
```

It exited `0` on the synchronized final base and reported matching raw,
normalized, and CAS hashes:

```text
raw_sha256        = sha256:85ace51c6a4dd01566ad4ee14028fc48bba25db190a01a8d09917eb4d6262f52
normalized_sha256 = sha256:85ace51c6a4dd01566ad4ee14028fc48bba25db190a01a8d09917eb4d6262f52
cas_ref           = sha256:85ace51c6a4dd01566ad4ee14028fc48bba25db190a01a8d09917eb4d6262f52
status            = match
```

The complete authoritative raw text is:

```text
**推论 20.4(隐藏运动二分)**〔closed〕。隐藏纤维变化只能作为

**离散素数地址跳转,或伴随 Σ_∞ 整体相位路径的变化**

出现;纯隐藏连续滑动非法,违者入账。(注意:Σ_∞ 连通而**非路径连通**——连续路径之可达域恰为单一流线,精确形态见定理 20.10 与推论 20.11;对偶层拓扑属账 O-4。)可见/隐藏之分(评注 10.4)由此获得动力学定理:**连续性居于可见侧,离散性居于隐藏侧**。
```

## Current candidate and receipt status

The canonical status command was run twice on the final base, first to obtain
the full unfiltered output and then with the same output redirected to an
isolated temporary file for exact machine parsing:

```sh
dotnet run --no-build \
  --project tools/StrataLint.Cli/StrataLint.Cli.csproj \
  --configuration Release -- \
  digest-status --formalize-candidates --base origin/dev
```

Both invocations exited `0`. The parsed result was:

```text
schema = stratalint-formalize-candidates-v3
ledger_sha256 = sha256:92c7b162f1956e991864a0aef8e84a34cd5983a9ef7b8f0107570bdd6e5745dc
match_count = 1
source_id = pzg-v170
ast_path = corollary/20.4
kind = corollary
cas_ref = sha256:85ace51c6a4dd01566ad4ee14028fc48bba25db190a01a8d09917eb4d6262f52
withheld_matches = []
```

Before this report was created, the exact-ID search over
`Meta/Digestion/formalizations` and `docs/devloop/reports` exited `1` with no
hit. A whole-tree exact-ID search, excluding `.git` and `.lake`, also exited
`1`. Thus the selected atom had no current formalization receipt, prior report,
or deposited coverage artifact; it remained the one exact formalization
candidate reported above.

## Clause-level statement echo

No source clause is omitted from this accounting.

| Authoritative clause | Required faithful Lean counterpart | Current evidence and disposition |
|---|---|---|
| `隐藏纤维变化只能作为 ... 或 ... 出现` | A carrier `HiddenChange` (or a source-justified existing carrier), predicates for both alternatives, and a theorem of the shape `∀ change, DiscretePrimeAddressJump change ∨ AccompaniedByGlobalPhasePath change` | Missing. No checked candidate introduced an arbitrary-change binder or an exhaustive disjunction. Choosing transitions, actions, paths, or endpoint pairs as the carrier would materially change the claim and is not determined by the source text. |
| `离散素数地址跳转` | A branch predicate characterizing which arbitrary hidden changes are discrete prime-address jumps | `discreteHiddenJump : ℤ →+ HiddenAddress` is one explicit nonzero integer action. Its own docstring says it is an anti-vacuity witness and does not classify all nontrivial hidden actions. One witness is not a branch classifier. |
| `伴随 Σ_∞ 整体相位路径的变化` | A branch predicate relating an arbitrary hidden change to a global phase path in the universal solenoid, plus a bridge from the change carrier to path endpoints | `path_joined_iff_real_flow_orbit` classifies joined solenoid point pairs by a real-flow orbit. It does not accept or classify an arbitrary hidden change, and no theorem connects every such change to its endpoint relation. |
| `纯隐藏连续滑动非法` | Rigidity for arbitrary continuous hidden paths/slidings, not only homomorphic real actions | Strong partial closure exists: `prime_adic_hidden_motion_rigidity` treats arbitrary continuous `unitInterval` paths, and `hidden_fiber_rigidity` treats arbitrary continuous maps from preconnected real subsets. `continuous_hidden_flow_eq_zero` is a narrower additive-real specialization. This clause alone does not yield the dichotomy. |
| `Σ_∞ 连通` | A `ConnectedSpace UniversalSolenoid` instance | Present and frozen in `D5/S1/Dynamics/UniversalSolenoid.lean`. |
| `非路径连通` | `¬ PathConnectedSpace UniversalSolenoid` | A substantive proof was checked in the rejected candidate, but it was not deposited because the encompassing theorem failed fidelity. No current deposited declaration was found by the focused search. |
| `连续路径之可达域恰为单一流线` | `Joined x y ↔ ∃ t, y = realFlow t + x` for arbitrary solenoid points | Exactly present as the frozen theorem `path_joined_iff_real_flow_orbit`. |
| `连续性居于可见侧,离散性居于隐藏侧` | A derived dynamical theorem whose quantifiers and carriers make the visible/hidden classification exhaustive | Missing for the same reason as the first row. Continuous hidden rigidity and a single discrete example do not establish an exhaustive visible/hidden dynamics classification. |

The dropped-or-weakened set for the rejected conjunction is therefore
nonempty: the universal hidden-change carrier, both branch predicates, the
`∀ change` binder, the `A change ∨ B change` conclusion, and the general bridge
from a hidden change to either branch are all absent.

## Strong frozen partial legs

The following declarations are substantive and separately frozen; none is
being reproved or modified here.

1. `D5/S1/Solenoid/HiddenMotionRigidity.prime_adic_hidden_motion_rigidity`

   ```lean
   (hiddenMotion : unitInterval → ∀ p : Nat.Primes, ℤ_[p.1]) →
   Continuous hiddenMotion → ∀ x y, hiddenMotion x = hiddenMotion y
   ```

   This is arbitrary path rigidity, not merely additive-flow rigidity. Freeze
   event:
   `Golden/Frozen/accepted/7b1891a1e3b89ad03abf0b55d5b46bc1a4c61b5d593133ef6e92e31ef27b7d3d.json`.

2. `D5/S3/Arith/HiddenFiberRigidity.hidden_fiber_rigidity`

   ```lean
   IsPreconnected s → ContinuousOn f s →
   ∀ x ∈ s, ∀ y ∈ s, f x = f y
   ```

   This covers arbitrary continuous maps from any preconnected real subset to
   the prime-adic hidden product. Freeze event:
   `Golden/Frozen/accepted/fcef716d211249ce297828f622bd1a0585f5177df32b5e99fc862f04b50e9cb0.json`.

3. `D5/S3/Observer/HiddenFlow/ContinuousRigidity.continuous_hidden_flow_eq_zero`

   ```lean
   (flow : ContinuousAddMonoidHom ℝ HiddenAddress) → flow = 0
   ```

   Its source explicitly says: "This excludes continuous real flows only; it
   does not classify other parameter groups or force them to be discrete."
   Freeze event:
   `Golden/Frozen/accepted/bf88d35e30cdc4b1dac52cb7d315ccbae1b04fccbc25056f9c0188dee25e64f1.json`.

4. `D5/S3/Observer/HiddenFlow/DiscreteRigidity.discrete_hidden_jump_is_nonzero_and_has_no_continuous_real_extension`

   This proves one canonical integer-cast jump is nonzero and has no continuous
   additive real extension. The general supporting theorem's source explicitly
   calls the result an "integer-grading obstruction, not a classification of
   arbitrary actions." Freeze event:
   `Golden/Frozen/accepted/7f4aeeea36b435af395bdd971b7ad08a9178cad9048188ecce5d63ce542f3ba7.json`.

5. `D5/S1/Solenoid/PathOrbitClassification.path_joined_iff_real_flow_orbit`

   ```lean
   Joined x y ↔ ∃ t : Real, y = UniversalSolenoid.realFlow t + x
   ```

   Freeze event:
   `Golden/Frozen/accepted/8a1247cabdb5c56d914c6f7e5ef996adb32693391dc797548edbf3df7171ac88.json`.

6. `D5/S1/Dynamics/UniversalSolenoid` supplies the frozen
   `ConnectedSpace UniversalSolenoid` instance. Freeze event:
   `Golden/Frozen/accepted/4f5b9489534b2744c9c0cdea5a3824380d1bea2d9d7d8b6609fa9693671a5f6b.json`.

These legs can be reused by a future faithful theorem. Their conjunction does
not create the missing classifier.

## Checked but non-deposited topology attempt

Before the fidelity rejection, the untracked candidate
`D5/S3/Observer/HiddenFlow/HiddenMotionDichotomy.lean` contained a proof of:

```lean
ConnectedSpace UniversalSolenoid ∧
  ¬ PathConnectedSpace UniversalSolenoid
```

The proof was checked on the then-current `4436226a` base by:

```sh
lake env lean /dev/stdin
lake build D5.S3.Observer.HiddenFlow.HiddenMotionDichotomy
make lean
```

All three commands exited `0`. Axiom inspection reported exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The proof strategy was substantive:

1. Embed each integer diagonally into compatible profinite residues.
2. Prove CRT assembly of the diagonal p-adic casts equals that integer residue.
3. Identify its kernel point with `UniversalSolenoid.realFlow (z : ℝ)`.
4. Define a split address with coordinate `0` at prime `2` and coordinate `1`
   elsewhere.
5. Use the prime-`2` coordinate to force any diagonal integer to be `0`, then
   the prime-`3` coordinate to derive `1 = 0`.
6. Apply `path_joined_iff_real_flow_orbit` and visible projection to show the
   split kernel point is not joined to zero.
7. Combine that witness with the existing connected-space instance.

This proves a valid topology component. It still does not quantify over hidden
changes or prove the two-branch dichotomy. After the reviewer rejected the
encompassing theorem, these three untracked artifacts were removed with
`apply_patch` and are not present in the final tree:

```text
D5/S3/Observer/HiddenFlow/HiddenMotionDichotomy.lean
Blueprint/D5/S3/Observer/HiddenFlow/HiddenMotionDichotomy.scribe.cs
Blueprint/D5/S3/Observer/HiddenFlow/HiddenMotionDichotomy.md
```

The old compile results are reported as attempt evidence, not as a current
deposited declaration or as final-base verification of a deleted file.

## Why the rejected conjunction is insufficient

The source's central clause has the logical shape:

```text
∀ change : HiddenChange,
  DiscretePrimeAddressJump change ∨
  AccompaniedByGlobalPhasePath change
```

The rejected candidate instead conjoined facts with different subjects:

```text
all continuous additive real hidden flows are zero
∧ one canonical integer jump is nonzero
∧ that jump has no continuous additive real extension
∧ the universal solenoid is connected
∧ the universal solenoid is not path connected
∧ joined point pairs are exactly one real-flow orbit
```

No conjunct introduces an arbitrary `change`, and no conjunct returns either
branch for such a change. Existential examples cannot establish a universal
classification; topological connectedness facts cannot manufacture a branch
predicate; and a theorem about additive real homomorphisms does not classify
all paths, actions, transitions, or other possible meanings of "change".

The missing bridge is not a routine proof gap. The source does not uniquely say
whether a hidden change is an address difference, a transition pair, a group
action, an endomorphism, or a path. Selecting one carrier without further
source evidence would alter the theorem's generality. Under the statement-echo
rule, this unresolved carrier ambiguity and the absent universal disjunction
force `open` before deposit.

## Search trace

The exact focused repository searches were:

```sh
rg -n -i \
  'hidden.*change|hidden.*motion|discrete.*jump|phase.*path|path.*phase|classif|dichotomy' \
  D5 -g '*.lean'
```

Exit `0`. Relevant hits were the hidden-motion rigidity, path-orbit
classification, continuous rigidity, and discrete rigidity modules. The broad
`classif` alternative also produced unrelated classification hits; those were
not treated as evidence.

```sh
rg -n \
  'prime_adic_hidden_motion_rigidity|hidden_fiber_rigidity|continuous_hidden_flow_eq_zero|discrete_hidden_jump_is_nonzero_and_has_no_continuous_real_extension|path_joined_iff_real_flow_orbit' \
  D5 -g '*.lean'
```

Exit `0`; all five exact declarations were found at the paths listed above.

```sh
rg -n -F \
  'pzg-residual-85ace51c6a4dd01566ad4ee14028fc48bba25db190a01a8d09917eb4d6262f52' \
  Meta/Digestion/formalizations docs/devloop/reports
```

Exit `1`; no prior receipt or report was found. The corresponding whole-tree
search excluding `.git` and `.lake` also exited `1` before this report existed.

A targeted carrier/interface search for `HiddenAddress`, `UniversalSolenoid`,
`realFlow`, kernel points, and profinite declarations exited `0`. It found the
existing equivalences and path decomposition interfaces, but no arbitrary
hidden-change carrier or exhaustive dichotomy theorem.

Targeted connectedness/path-connectedness search exited `0`; it found the
`ConnectedSpace UniversalSolenoid` instance and the path-orbit theorem but no
deposited `PathConnectedSpace` negation.

Freeze-event searches for `ContinuousRigidity.lean`, `DiscreteRigidity.lean`,
`HiddenMotionRigidity.lean`, `HiddenFiberRigidity.lean`,
`PathOrbitClassification.lean`, and `UniversalSolenoid.lean` each exited `0`
and resolved to the accepted events listed above.

One stale-path probe attempted to search `Meta/BACKFILL.yaml` and exited `2`
because that path does not exist in the current repository. It was not treated
as ledger evidence. The live `digest-status --formalize-candidates` command and
its content-addressed ledger SHA are the authoritative current status evidence.

No third-party Lean ecosystem search was run. The task stopped at statement
echo because the source-faithful carrier and exhaustive classifier were
undefined; external theorem lookup cannot resolve that local semantic choice.

## Fidelity and non-hollowness checklist

- **Conclusion substance:** the intended exhaustive dichotomy is substantive,
  not `True`, definitionally `True`, or a hypothesis restatement. The rejected
  conjunction also contains substantive theorems, but it is a different and
  weaker conclusion.
- **Hypothesis satisfiability:** not run for a source-faithful candidate. No
  faithful `HiddenChange` carrier or candidate signature was defined, so there
  is no honest hypothesis witness to elaborate. The checked topology component
  was hypothesis-free but does not discharge the target.
- **Domain inhabitance:** not run for a source-faithful combined domain. The
  existing `HiddenAddress` and `UniversalSolenoid` types are inhabited, and the
  checked split address gives a nontrivial topology witness, but selecting one
  of those as the source's arbitrary-change carrier is exactly the unresolved
  ambiguity.
- **Proof substance:** the frozen partial legs and the checked non-path proof
  have real mathematical content and standard axiom closure. They cannot derive
  the absent `∀ change, A change ∨ B change` theorem by conjunction.
- **Duplicate search:** exact declaration and atom-ID searches found reusable
  partial legs but no exact formalization, receipt, or prior report for this
  atom.
- **Clause fidelity:** failed. The arbitrary-change carrier, both alternative
  predicates, the universal binder, the disjunction, and the general bridge are
  missing. Deposit is blocked.
- **Rendered-statement fidelity:** not run. The rejected Lean/Scribe/Markdown
  candidate was deleted, so no candidate rendering remains to compare, and no
  source-faithful declaration exists to render.

No unavailable checklist item is passed as verified or replaced by an
`ASSUMED-UNVERIFIED` completion claim. The failed clause-fidelity item forces the
`open` outcome.

## Grader-trap checklist

- **Conjunction vs dichotomy:** several true conjuncts do not prove a universal
  disjunction about every hidden change.
- **Witness vs classification:** `discreteHiddenJump` witnesses one nonzero
  integer action; it does not classify all hidden changes as discrete jumps.
- **Additive flow vs arbitrary motion:** zero continuous additive real
  homomorphisms are narrower than arbitrary continuous hidden paths. The
  broader path-rigidity theorems are accounted for separately and still do not
  yield the dichotomy.
- **Point-pair orbit vs change branch:** `Joined x y ↔ ∃ t, ...` classifies
  solenoid point pairs. A bridge from an arbitrary hidden change to such a pair
  is required and missing.
- **Connected/non-path-connected vs exhaustive dynamics:** topology components
  do not define either branch predicate or select a branch for every change.
- **Compile green vs fidelity green:** the deleted candidate compiled, but Lean
  compilation and standard axiom closure do not certify that it proved the
  echoed source statement.
- **Stronger-component language:** no partial theorem is described as a
  strengthening of the source unless a checked carrier map preserves all
  quantifiers and clauses. No such map exists here.
- **Status projection vs closure:** appearing once in the formalization
  candidate list is evidence that the atom remains selectable, not that it is
  covered or closed.

## Final disposition

Decision: retain the atom as `open`. A future faithful closure needs, before
proof work:

1. A source-justified formal carrier for arbitrary hidden changes.
2. Exact predicates for discrete prime-address jumps and changes accompanied by
   global solenoid phase paths.
3. A general bridge/classifier proving the universally quantified disjunction.
4. Only then, reuse of the already frozen path-rigidity, integer-obstruction,
   connectedness, and path-orbit components, plus a separately deposited
   non-path-connectedness theorem if needed.

`make deposit`, `make cover`, and `make preflight` were not run because clause
fidelity failed before deposit. No push was made and no pull request was opened.
