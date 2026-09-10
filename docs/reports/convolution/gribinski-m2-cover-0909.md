# Frozen Gribinski degree-two coverage audit

## Provenance and scope

- Skill context: no skill invoked by this worker; direct Codex implementation
  in the runner's `gribinski-m2-cover-0909/attempt-1` implementation seat.
- Carrier and division: this Codex worker reads the atom bytes, audits fidelity,
  invokes the coverage writer, and performs the local checks. No independent
  review seat or other model family is claimed.
- Mixing: sequential worker audit and implementation, zero review votes. The
  user supplied the frozen-module observation and candidate declaration names;
  the observations below were checked locally, not inferred from that input.
- Form: `cover`. Source: `quantum-rh`. No Lean edits, deposit, freeze, atom
  rewrite, or Scribe edits are authorized by this task. No auto-merge.
- Audit baseline: `b9ad72010f6473b22e7616958a7e78db6fe0d2e2` (HEAD and origin/dev
  at the initial read). Candidate declarations were read with
  `git show origin/dev:D5/S3/Zeros/Convolution/GribinskiDegreeTwo.lean`, including
  every binder and conclusion through `:= by`.
- Frozen membership exists at
  `Golden/Frozen/state/D5/S3/Zeros/Convolution/GribinskiDegreeTwo.lean.json`;
  its recorded module statement ID is
  `sha256:184c298cb6b3a6b32640e84511f41eede52d8d0d29ae2b24a68f14ef5722487e`.

All declaration names below have prefix
`D5/S3/Zeros/Convolution/GribinskiDegreeTwo.`.

## Fidelity criterion and shared notation

Every mathematical clause in each selected atom must be supplied by the listed
frozen declarations, with the same quantifier direction, inequalities and
parameter domain. `verbatim` means the same mathematical formula after variable
and notation transcription; `equivalent` requires the stated definitional or
algebraic identification. Any `not-covered` clause forbids a whole-atom claim.
The coverage command does not judge these identifications or source fidelity.
Its `partial-closed` state must not be used as a fidelity verdict.

The three full atom IDs resolve uniquely to the `quantum-rh` ledger. Initial
entries are `residual-open`, have `coverage_gids: []` and
`receipts.unresolved_subitems: []`, and have no `chain_atoms` field. Thus there
are no child atoms to cover and no reason to introduce a container theorem.
The raw text printed by `make show-atom` is the authority for each obligation.

The surrounding source supplies notation, without adding obligations to the
three atom bodies: `QUANTUM-RH.md:60814` defines
`kappa(alpha)=(alpha+1)/(2*(alpha+2))`; `:60821` explicitly defines
`P_2(R_{>=0})` as the monic real quadratics `(X-a)(X-b)` with `a,b>=0`.
Consequently membership is exactly `exists r s : Real, 0 <= r /\ 0 <= s /\
p = rootPair r s`. It requires neither distinct nor strictly positive roots,
and does not allow a nonunit leading scalar. Lean `rootPair` at line 81 uses
`(X-C a)*(X-C b)`, where `C` embeds the real constants in `Real[X]`.

The old surrounding transcription of Definition 3.10 used a ratio prefactor.
The appended erratum at `QUANTUM-RH.md:61194` explicitly corrects it to the
product of falling factorials and explicitly states that G1-G4's conclusions
are unchanged. Lean `weight`, `normalizedCoeff`, `convolutionCoeff`, `boxplus`
(lines 65-79) use that product definition before root specialization;
`normalized_coefficient_convolution` (line 103) states its normalized coefficient
identity for all `k<=2` on the nonsingular domain. This audit uses that recorded
correction to identify the shared operator. It does not cover or validate the
obsolete ratio formula. The external paper was not independently re-fetched
in this coverage-only task.

## G1

Atom: `7901adf784a2db15b73b33751c521fc703f8bbe431efb0304c449cfa3b049907`.
Edge target: `D5/S3/Zeros/Convolution/GribinskiDegreeTwo.g1_explicit_coefficients`.

| Atom clause | Lean binder or conclusion | Match |
| --- | --- | --- |
| `alpha in R \\ {-1,-2}` | `(alpha : Real) (h1 : alpha != -1) (h2 : alpha != -2)`, lines 136-137 | verbatim |
| `a,b,c,d in R` universally | `(a b c d : Real)`; no sign, order, integrality or distinctness assumption | verbatim |
| `p=(X-a)(X-b), q=(X-c)(X-d)` | Inputs `rootPair a b`, `rootPair c d`; expand line 81 | equivalent |
| `p boxplus_2^alpha q` | `boxplus alpha (rootPair a b) (rootPair c d)` with the product definition identified above | equivalent |
| `X^2-(a+b+c+d)X+[ab+cd+kappa(alpha)(a+b)(c+d)]` | Entire conclusion at lines 138-140; `C` embeds the coefficient sum and constant term | verbatim |

Fidelity verdict: **passed**. No missing clause. The parameter domain is exactly
the nonsingular domain, not the stronger `alpha>-1` condition.

Coverage execution: `make cover` exited 0. Transition:
`residual-open -> absorbed-closed`, `deletable=true`, no gaps, as printed by the
writer's `ENTRY quantum-rh/7901...` line (`g1-cover.log`). The resulting edge
binds target statement
`sha256:f0c48dabfe28b97557cf918888a05d1312ee879f080238ed386cd9726773f78a`.
`make show-atom` after the write exited 0 and printed the original body and
this single coverage GID (`g1-after.log`). Scribe emitted zero changed
blueprints. The complete G1 unit is committed and pushed before G3 starts.

## G3

Atom: `8ef6b9257471235dae81e95cd49a82d8589c77b60cfb90cd4d4355ed0ae75092`.
Edge target: `D5/S3/Zeros/Convolution/GribinskiDegreeTwo.g3_nonnegative_roots`.

| Atom clause | Lean binder or conclusion | Match |
| --- | --- | --- |
| Every real `alpha>-1` | `(alpha : Real) (halpha : -1 < alpha)`, line 202 | verbatim |
| Every `p,q in P_2(R_{>=0})` | Universal `a b c d : Real`, four separate hypotheses `0<=a`, `0<=b`, `0<=c`, `0<=d`; inputs `rootPair a b`, `rootPair c d` | equivalent |
| Output belongs to `P_2(R_{>=0})` | `exists r s : Real, 0<=r /\ 0<=s /\ output = rootPair r s`, lines 204-205 | equivalent |
| Boxed `forall alpha>-1, forall a,b,c,d>=0, exists r,s>=0` with the factorization | Full theorem type, lines 202-205; all input quantifiers precede the output witnesses | verbatim |
| Membership formulation is equivalent to the boxed formulation | Expand the explicit source membership definition and Lean `rootPair` in both directions | equivalent |

Fidelity verdict: **passed**. The parameter is real, not integer or restricted
to `alpha>=0`; `-1<alpha<0` is included. Nonnegative means `<=`, not `<`.
For any member `p` the source definition supplies its two nonnegative root
witnesses, and the same holds for `q`; the theorem then supplies the output
witnesses. Conversely those witnesses give membership by the same definition.
Root order and multiplicity impose no further conditions, and no leading
scalar is lost because the source class is explicitly monic.

Coverage execution: `make cover` exited 0. Transition:
`residual-open -> absorbed-closed`, `deletable=true`, no gaps (`g3-cover.log`).
The edge binds target statement
`sha256:9b52a48a8690b1a5f3fd750f75a9e2e0b369fc84a49c9e74192b7297a9733c3d`.
The subsequent `make show-atom` exited 0 and printed the original body and
this single coverage GID (`g3-after.log`). The Lean report was a cache hit and
Scribe emitted zero changed blueprints. This atom is committed and pushed
before starting G4 coverage.

## G4

Atom: `ff5edc2fa518d7aad2e434878eaed431d77462514fb23ba7bdbc47c5183d425e`.
Four edge targets, all with the module prefix above:
`g4_parameter_range_sharp`, `g4_negative_product`,
`g4_negative_discriminant`, `preservation_iff`.

| Atom clause | Lean binder or conclusion | Match |
| --- | --- | --- |
| Every `alpha in R \\ {-1,-2}` with `alpha<-1` | `g4_parameter_range_sharp`: `(alpha : Real) (_h1 : alpha != -1) (h2 : alpha != -2) (halpha : alpha < -1)`, lines 270-271 | verbatim |
| Exist `a,b,c,d>=0` such that output is outside `P_2(R_{>=0})` | Same theorem: existential quadruple with four nonnegativity conjuncts, followed by `not (exists r s : Real, 0<=r /\ 0<=s /\ output=rootPair r s)`, lines 272-274 | equivalent |
| First family, for `-2<alpha<-1`, exact tuple `(1,0,1,0)` | `g4_negative_product`: strict `hlo`, `hhi`, and `rootPair 1 0` twice, lines 223-227 | verbatim |
| First family has root product `kappa(alpha)<0` | Its first two conjuncts give `output.coeff 0=kappa alpha` and `kappa alpha<0`; the last denies nonnegative factorization | equivalent |
| Second family, for `alpha<-2`, exact tuple `(1,1,1,1)` | `g4_negative_discriminant`: strict `halpha` and `rootPair 1 1` twice, lines 243-246 | verbatim |
| Second family has `D=8*(1-2*kappa(alpha))<0` | Its first two conjuncts give exactly that equality and strict negativity for `discriminant alpha 1 1 1 1` | equivalent |
| Both explicit families are required | Both family declarations are separate edge targets, with their own stated parameter intervals and tuples | verbatim |
| On the nonsingular domain, preservation for all input members iff `alpha>-1` | `preservation_iff`: `(alpha : Real) (h1 : alpha != -1) (h2 : alpha != -2) : preservesNonnegativeRoots alpha <-> -1 < alpha`, lines 286-287 | equivalent |

For the first family's root-product wording, G1 specializes the actual output
to `X^2-2*X+kappa`. It is monic and has discriminant `4-4*kappa>0` on the
stated interval. Vieta identifies the product of its two real roots with its
constant coefficient. This is a mathematical identification in the audit,
not a claim that `g4_negative_product` literally quantifies a pair of roots.

For the second family's `D`, frozen `discriminant_eq_output` (lines 149-155)
identifies the named discriminant with the actual polynomial's coefficient
discriminant. Its parameter exclusions follow from `alpha<-2`. The family
theorem additionally proves `forall x : Real, output.eval x != 0`; the atom
only requires the discriminant certificate.

For the boxed equivalence, expand `preservesNonnegativeRoots` (lines 217-220).
It universally quantifies the input root quadruple and then existentially
quantifies the two nonnegative output roots. The source's explicit membership
definition gives precisely the quantification over `p,q`. Both directions of
the iff are present; neither `alpha=-1` nor `alpha=-2` is silently added.

Fidelity verdict: **passed for the four declarations collectively**. The
generic sharpness theorem alone would be **partial**: its type does not name
either required tuple or assert the boxed iff. All four existing declarations
are supplied together in one `make cover-batch` invocation, four TSV rows with
the same complete atom ID. No chain child or container theorem is invented.

Coverage execution: `make cover-batch` exited 0 and reported
`status=applied`, `lines=[1,2,3,4]`, `reason=coverage committed` (`g4-cover.log`).
The canonical writer moved the atom from `residual-open` to `absorbed-closed`;
the resulting YAML contains exactly the four requested targets, each with a
nonnull `target_statement_id`, and empty `unresolved_subitems`.
`make show-atom` after the write exited 0 and printed the unchanged raw body
and all four GIDs (`g4-after.log`). It does not print migration state in this
revision. The Lean report was a cache hit and Scribe emitted zero changed
blueprints. This atom is committed and pushed before opening the PR.

### Body boundary

The adjacent proof prose at `QUANTUM-RH.md:60920` says the two families never
serve as counterexamples on each other's interval. This is outside the selected
G4 atom's raw body and is false: in the first family at `alpha=-5/2`,
`kappa=3/2` and the output discriminant is `-2`; in the second family at
`alpha=-7/4`, `kappa=-3/2` and the output root product is `-4`
(discriminant `32`). These exact rational calculations were performed with
Ruby `Rational`, exit 0. They do not contradict either interval-specific
certificate in the selected atom. This coverage makes no claim that the full
failure domains are disjoint, or that the surrounding proof prose is covered.
No source or atom bytes are modified to hide this boundary.
The false exclusivity paragraph has its own residual-open atom
`472c518b2c7bcded4c45d75d7150de316adede819766976d516500f0730b6be1`
and is also contained in proof atom
`eda6834ae2cdf6972f24c33bcae509a0d57c84769a6728b17fc514024058dbd2`.
Neither is a target of this task or receives a coverage edge here.

## Command evidence

Attempt logs are under
`/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/gribinski-m2-cover-0909/attempt-1`.

- Initial `make show-atom` for each of the three atoms: exit 2; the fresh tree
  had no built `tools/StrataLint.Cli/bin/Release/net10.0/StrataLint` executable.
- `make -C tools dotnet`: exit 0, zero warnings and errors (`dotnet-build.log`).
- Repeated `make show-atom` with each full ID: exit 0; complete raw bodies and
  empty coverage printed (`g1-before.log`, `g3-before.log`, `g4-before.log`).
  In this repository revision `show-atom` does not print a derived migration
  verdict, even after the report exists. Migration evidence therefore comes
  from the writer's `ENTRY` verdict and the actual ledger directory names;
  `show-atom` independently confirms the body and coverage targets.
- `git -C /Users/auricstudio/trureturing pull --ff-only origin dev`: exit 0,
  already up to date; the task continues in the supplied isolated worktree.

The worker stdout log retains the tool calls and their actual exit codes.
An initial lowercase source-path glob failed in zsh; reading `source.toml`
resolved the canonical uppercase path `docs/develop/theory/QUANTUM-RH.md`.
The first `make cover` used the canonical warm donor (`method=clonefile`, both
olean states warm), produced a delta report (`changed=0 added=13 recheck=13`),
then wrote the edge. The full command log contains the writer's whole-ledger
diagnostic output; only the target's `ENTRY` line is used for this transition.

## Push checkpoints

G1: `1818679f5a56866c77f81ee25af86768c1cb1b94`, commit and push both exited 0.
The remote branch was created before beginning G3 coverage.

G3: `25cea42bdbd8d423b6d5035e1e85f829f3f30365`, commit and push both exited 0.
The remote branch was updated before beginning G4 coverage.

G4: this section travels in the G4 coverage commit. The actual SHA and push
receipt are recorded in the attempt's `result.json` and the PR description,
after the commit exists.

## Delivery boundary

All three selected atom bodies pass the clause audit, collectively using four
GIDs for G4; none of their mathematical clauses is left unrepresented. All
three now have the machine-derived `absorbed-closed` ledger location.
This does not mean the coverage writer judged fidelity. Source membership and
root-product identifications are explicit mathematical reasoning in this audit,
not newly compiled Lean bridge proofs or independent model review.

Only the three ledger entries and this report are intended tracked changes.
The baseline-to-current diff for `*.lean`, `Golden/Frozen/**`, `Blueprint/**`,
atom CAS blobs and theory sources was empty. Before PR opening, a fresh fetch
gave origin/dev `444e07abe3c6affc7985f4097084759656d0176d`; its increment from
the audit baseline changed none of the target entries, frozen module or pin.
PR checks and remote commit identities are recorded in the final result;
this task stops with an open PR and does not authorize merging.
