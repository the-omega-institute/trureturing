# Interface theorem 3.9 linear-margin atom: open report

## Disposition

`open`.

The selected atom is not closed by the existing diagonal KL declarations. The
repository has a close finite inequality and an asymptotic vanishing theorem,
but the source atom also carries a probability-space/model clause, the
`D_a`/`B_a` binomial derivation, and a concrete `A = 12` observation. No single
faithful declaration or observation receipt for all of those clauses exists.
The finite inequality alone is therefore not being deposited as a weakened
replacement.

No Lean, Blueprint, Scribe, receipt, frozen-ledger, or digestion file was
modified by this report.

## Environment and atom selection

The repository was checked in the assigned checkout:

```text
pwd = /Users/mstudio3/trureturing
branch = dev
HEAD = 0e23f3412a0cfd4d6b4865209097c7ad1e766d73
origin/dev = 0e23f3412a0cfd4d6b4865209097c7ad1e766d73
```

Baseline commands:

```text
git merge-base --is-ancestor origin/dev HEAD
merge_base_rc=0
make dotnet
make_dotnet_rc=0
```

The formalization skill requested `Meta/StrataLint/scripts/local-harness-gate.sh`,
but that path is absent in this checkout. No PATH mutation was made; the
absolute system tools used here completed successfully.

The authoritative atom was selected from
`docs/develop/theory/INTERFACE_PAPER.md`, `theorem/3.9`, and obtained through:

```sh
make show-atom \
  ATOM_ID=pzg-residual-c5c287b312bdc7472e773122a959f90694baa798a18b4c030051705db43fff60
```

The command exited `0` and reported:

```text
SHOW_ATOM atom_id=pzg-residual-c5c287b312bdc7472e773122a959f90694baa798a18b4c030051705db43fff60 source_id=interface-v1 source_path=docs/develop/theory/INTERFACE_PAPER.md atomizer=pzg-v1 ast_path=theorem/3.9
HASH_VERIFY raw_sha256=sha256:c5c287b312bdc7472e773122a959f90694baa798a18b4c030051705db43fff60 normalized_sha256=sha256:c5c287b312bdc7472e773122a959f90694baa798a18b4c030051705db43fff60 cas_ref=sha256:c5c287b312bdc7472e773122a959f90694baa798a18b4c030051705db43fff60 status=match
```

The complete `BEGIN_RAW_TEXT` returned by that command is:

```text
**定理 3.9(线性边距)。** 沿定理 3.8 之记号,对 0 < α < (n−1)/n,且 A 充分大使 αA/(A−1) < (n−1)/n:
$$ \Pr\left[\min_a D_a < \alpha A\right] \le A\, e^{-(A-1)\, \mathrm{KL}\left(\tfrac{\alpha A}{A-1} \middle\| \tfrac{n-1}{n}\right)} \to 0, $$
故对角点渐近几乎必以线性边距逃逸,且边距密度趋于典型值 (n−1)/n:**对角点不仅逃逸,且以典型点的距离轮廓逃逸**。*证明*:写 p := (n−1)/n;由定理 3.8,D_a ≥ B_a 且 B_a ∼ Bin(A−1,p),故单项 Chernoff 以阈值参数 αA/(A−1) 给界,再取联合界。∎(A = 12 实测集中带 [0.17, 0.42]·A [机验]。)
```

No formalization receipt was found:

```sh
rg -n -F \
  'pzg-residual-c5c287b312bdc7472e773122a959f90694baa798a18b4c030051705db43fff60' \
  Meta/Digestion/formalizations
```

This produced no output.

## Clause-level echo

| Source clause | Intended formal counterpart | Evidence/status |
|---|---|---|
| “Along theorem 3.8 notation” | A declaration importing or defining the theorem-3.8 sample space, diagonal distances `D_a`, and the associated random experiment | **Missing.** No exact source-model/GID mapping was found. |
| `0 < alpha < (n-1)/n` | Real hypotheses on `alpha` and `n`, with `n` inhabited and the ratio well-defined | The existing theorems have analogous real hypotheses, but not this source model. |
| Sufficiently large `A` with `alpha*A/(A-1) < (n-1)/n` | A quantified/eventual or explicit adjusted-threshold hypothesis | The finite library theorem has the adjusted-threshold inequality, but only for its own finite-cardinality model. |
| `Pr[min_a D_a < alpha*A]` | Probability of the minimum of the source experiment's `D_a` variables | **Missing.** Existing `marginFailureProbability` is a finite uniform cardinality ratio over `g : A -> A -> Y`; it is not a declared source probability space with `D_a`. |
| `<= A * exp (-(A-1) * KL(...))` | The displayed finite KL/Chernoff union bound | Substantially covered by frozen `MarginBound.linear_margin_bound`, subject to the model mismatch above. |
| `... -> 0` | An asymptotic statement as `A` grows | Substantially covered by frozen `MarginVanishing.linear_margin_bound_tendsto_zero` and `margin_failure_probability_tendsto_zero`, again for the repository's finite-cardinality definition. |
| “therefore ... almost surely escapes with linear margin” and typical density `(n-1)/n` | The source-level interpretation, or a two-sided probability theorem | `TypicalDensity.typical_density_failure_probability_tendsto_zero` gives a stronger two-sided result for the repository model, but does not supply the missing source-model bridge. |
| Proof: `p := (n-1)/n`; theorem 3.8 gives `D_a >= B_a` | A checked coupling/order lemma between source variables | **Missing.** No `D_a`/`B_a` declarations or inequality were found. |
| `B_a ~ Bin(A-1,p)` and single-term Chernoff | A probability-law identification for each `B_a` | Existing files use `Bin(Real, r, p)` as an analytic bound, not a law for source variables `B_a`. |
| “then take the union bound” | A finite union event/probability lemma over `a` | Generic finite union machinery exists, but no theorem applies to the unintroduced source events. |
| `(A = 12)` measured band `[0.17, 0.42] * A [机验]` | A reproducible observation artifact and receipt with inputs, seed/method, and output | **Missing.** No matching observation artifact or receipt was found. |

The dropped-or-weakened set is nonempty: the source probability model, the
`D_a`/`B_a` law and domination, and the `A=12` observation cannot be mapped to
the existing declaration without changing the claim.

## Library search

The following searches were run verbatim.

```sh
rg -n "linear_margin_bound_tendsto_zero|margin_failure_probability_tendsto_zero|linear_margin_bound" \
  D5/S0/Diagonal/*.lean
```

Hits:

```text
D5/S0/Diagonal/MarginBound.lean:424:theorem linear_margin_bound ...
D5/S0/Diagonal/MarginVanishing.lean:44:theorem linear_margin_bound_tendsto_zero ...
D5/S0/Diagonal/MarginVanishing.lean:97:theorem margin_failure_probability_tendsto_zero ...
D5/S0/Diagonal/TypicalDensity.lean:498:theorem typical_density_failure_probability_tendsto_zero ...
```

```sh
rg -n "D_a|B_a|Bin\\(|iIndep|independent|ProbabilitySpace|Pr\\[|marginFailureProbability" \
  D5 Mathlib 2>/dev/null | head -120
```

The relevant hits were confined to the existing diagonal machinery, especially
`D5/S0/Diagonal/MarginBound.lean`, `MarginVanishing.lean`, and
`TypicalDensity.lean`; no source `D_a`, `B_a`, probability-space, or independence
declaration was found.

```sh
rg -n "A = 12|0\\.17|0\\.42|concentration band|机验" \
  docs/develop/theory/INTERFACE_PAPER.md D5 Evidence Meta
```

This found the source prose but no tracked observation artifact or receipt for
the `[0.17, 0.42] * A` band.

The atom-specific receipt search above was empty. The existing finite result is
not a duplicate of the complete atom because it has a different probability
definition and no source-variable derivation.

## Existing declarations and frozen constraints

`D5/S0/Diagonal/MarginBound.lean` defines
`marginFailureProbability` as a finite uniform ratio over
`{g : A -> A -> Y // exists a, hammingDistance f g a < alpha * card A}`.
Its frozen theorem `linear_margin_bound` (lines 422-542) proves the same
corrected KL-shaped upper bound for that definition.

`D5/S0/Diagonal/MarginVanishing.lean` defines the corresponding
`linearMarginBound` and freezes both
`linear_margin_bound_tendsto_zero` (lines 43-85) and
`margin_failure_probability_tendsto_zero` (lines 95-113).

`D5/S0/Diagonal/TypicalDensity.lean` freezes
`typical_density_failure_probability_tendsto_zero` (lines 496-540), a stronger
two-sided typical-density convergence theorem for the same finite listing
model.

The frozen records are:

```text
Golden/Frozen/accepted/10ee8f8885cf7cc9c4b985090e7135ef3c3486202967d458486ba7e9f7508f3a.json  (MarginBound)
Golden/Frozen/accepted/00ba7bdbced43a63c34287e5911742301dfcaf81f757131fd7867fd565735ae8.json  (MarginVanishing)
Golden/Frozen/accepted/d68d2ccdb730ecb20d5d0d7aab2f8f314cb73370882abc9d3fb034b73d6a9f0d.json  (TypicalDensity)
```

The exact ledger check was:

```sh
for p in D5/S0/Diagonal/MarginBound.lean \
         D5/S0/Diagonal/MarginVanishing.lean \
         D5/S0/Diagonal/TypicalDensity.lean; do
  printf '%s: ' "$p"
  grep -l -F "$p" Golden/Frozen/accepted/*.json
done
```

It returned the three records above. Adding the missing declaration to any of
those modules is prohibited by the active Freeze events. Reattestation would
not permit adding a declaration, so the frozen modules cannot be used as an
escape hatch for this atom.

## Fidelity gate

This is an `open` report, so the deposit gate is intentionally not claimed
green:

- Conclusion substance: the source conclusion is nontrivial, but no faithful
  Lean declaration was produced.
- Hypothesis satisfiability: no compiling witness for the source probability
  model and adjusted threshold was produced.
- Domain inhabitance: no source sample-space/domain declaration was produced.
- Proof substance: no new proof was written; the existing finite proof cannot
  discharge the missing semantic clauses.
- Duplicate search: completed above; the complete atom is not an existing
  declaration under another name.
- Clause fidelity: failed for the missing model, `D_a`/`B_a` derivation, and
  observation clauses; this blocks deposit.
- Rendered-statement fidelity: not run because no Lean/Scribe declaration was
  created.

The finite KL bound and asymptotic machinery are useful prerequisites, but
calling them the complete theorem would weaken the selected atom. A future
closure must first define the source probability experiment and variables,
prove the `D_a >= B_a`/binomial-law bridge and union event, and attach a
reproducible `A=12` observation receipt (or explicitly split that observation
into a separately tracked residual).

## Unreached workflow steps

Because the fidelity gate is not complete and the disposition is `open`, these
commands were not run:

```text
make deposit ATOM_ID=pzg-residual-c5c287b312bdc7472e773122a959f90694baa798a18b4c030051705db43fff60 GID=<gid>
make preflight
make cover ATOM_ID=pzg-residual-c5c287b312bdc7472e773122a959f90694baa798a18b4c030051705db43fff60 GID=<gid>
make pr-open ...
```

No declaration GID exists for this atom. `git diff --check` and `make
selftest` are run after this report is written; no deposit, preflight, cover,
or PR-opening door is appropriate for the current disposition.
