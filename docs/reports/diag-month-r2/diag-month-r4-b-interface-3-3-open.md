# Diagnostic Month R4 Lane B: Interface Theorem 3.3 Open Report

> **Historical erratum (P2):** This report is preserved as evidence for the
> implementation inspected at its recorded baseline. The
> `BaselineCoverageGids` rejection, baseline-occupied-GID rejection, and
> hosted-extension cross-atom/AST-path guard described below **已于 P2 删除**.
> They are not live cover behavior: coverage is now M:N, and reuse on another
> atom is allowed when that independent `(atom_id, GID)` edge has its own
> base-owned formalization precommitment plus valid coverage/Scribe receipts.
> References below to the "live", "current", or "canonical" cover rejection
> are historical statements at commit `470491ca088663eeebf36415db7f65af3dc415ec`,
> not claims about the present architecture. The mathematical bridge gaps and
> this lane's historical `open` outcome remain unchanged.

Outcome: `open`, with no formalization deposit or cover. A frozen theorem proves
the countable-family nullity mechanism, but it does not check two source-level
bridges, and the canonical cover path also rejects reuse of its already-bound
GID. No Lean declaration, Scribe source, receipt, or protected-ledger edit was
made.

## Baseline and atom

- Lane: `harness/diag-month-r4-b` at
  `/Users/mstudio3/trureturing-diag-month-r4-b`.
- Initial synchronized base: `470491ca088663eeebf36415db7f65af3dc415ec`;
  `HEAD` and `origin/dev` were equal before this report, and
  `git merge-base --is-ancestor origin/dev HEAD` exited `0`.
- Atom ID:
  `pzg-residual-9ba51e073a6b7bfd395328fa2968c377a5539d3df64ffcd36797cf9a7faa3548`.
- Source: `interface-philosophy-v4`,
  `docs/develop/theory/INTERFACE_PHILOSOPHY.md`, `theorem/3.3`.
- Atomizer: `pzg-v1`.
- Claim class: theorem/bridge; a single-system full-measure claim plus its
  countable-tower strengthening.

The authoritative command

```sh
make show-atom ATOM_ID=pzg-residual-9ba51e073a6b7bfd395328fa2968c377a5539d3df64ffcd36797cf9a7faa3548
```

exited `0` with:

```text
SHOW_ATOM atom_id=pzg-residual-9ba51e073a6b7bfd395328fa2968c377a5539d3df64ffcd36797cf9a7faa3548 source_id=interface-philosophy-v4 source_path=docs/develop/theory/INTERFACE_PHILOSOPHY.md atomizer=pzg-v1 ast_path=theorem/3.3
HASH_VERIFY raw_sha256=sha256:9ba51e073a6b7bfd395328fa2968c377a5539d3df64ffcd36797cf9a7faa3548 normalized_sha256=sha256:9ba51e073a6b7bfd395328fa2968c377a5539d3df64ffcd36797cf9a7faa3548 cas_ref=sha256:9ba51e073a6b7bfd395328fa2968c377a5539d3df64ffcd36797cf9a7faa3548 status=match
BEGIN_RAW_TEXT
**定理 3.3(常道守恒)[证]。** 对任一命名系统:μ(A(𝒩)) = 1。且若 (𝒩_k)_{k∈ℕ} 为任一扩张塔(N₀ ⊆ N₁ ⊆ ⋯,各层可数,ν 相容延拓),则极限系统之匿名集仍满测度。
*证明。* ν(dom ν) 是可数集的像,至多可数;μ 无原子故 μ({x}) = 0 对一切 x ∈ X,可数可加性给出 μ(ν(dom ν)) = 0,故 μ(A) = 1。塔的情形:⋃_k ν_k(dom ν_k) 为可数多个可数集之并,仍可数,同理零测。∎
END_RAW_TEXT
```

The normalized text is byte-for-byte the same text. The raw, normalized, and
CAS hashes are the exact machine output and all match.

## Partial frozen carrier

The closest already frozen declaration is

```text
D5/S0/Naming/Conservation/NamingTowerConservation.countable_tower_anonymous_full_measure
```

whose Lean source signature is:

```lean
theorem countable_tower_anonymous_full_measure
    {X : Type u} [MeasureSpace X] [Uncountable X]
    [NoAtoms (volume : Measure X)] [SigmaFinite (volume : Measure X)]
    {J : Type v} [Countable J] (systems : J -> NamingSystem X) :
    (Set.iUnion fun j => (systems j).named).Countable /\
      volume (Set.iUnion fun j => (systems j).named) = 0 /\
      volume (Set.iUnion fun j => (systems j).named)ᶜ =
        volume (Set.univ : Set X)
```

The historical pre-merge raw Lean report records `kind=theorem` and exactly the
standard axiom closure `{Classical.choice, Quot.sound, propext}`. Freeze event
`Golden/Frozen/accepted/ede6971b3c411fdc6e6112621f6515f2636dba8a4441eba63dccadb69241e638.json`
pins the declaration at deposit commit
`166af8c9b899a01292d7eb51591f38ab36c25354`.

Its repository carrier is:

```lean
structure NamingSystem (X : Type u) [MeasureSpace X] where
  Name : Type v
  assignment : Name -> Option X
  height : Name -> Nat
  finite_layer : forall Q, Set.Finite {n | height n <= Q}

def NamingSystem.named (system : NamingSystem X) : Set X :=
  {x | exists n, system.assignment n = some x}
```

The source's countable names are represented by finite height sublevels;
`name_layer_finite` derives `Countable system.Name`. Its atomlessness assumption
matches the carrier's `NoAtoms` mechanism. However, the source fixes a Borel
probability measure while this theorem has no `IsProbabilityMeasure` binder and
does not expose a checked specialization proving `volume Set.univ = 1`.
Therefore its generic conclusion `volume complement = volume univ` does not by
itself discharge the source's numeric equality `mu(A) = 1`.

## Clause echo

| Source obligation | Exact formal discharge |
|---|---|
| Arbitrary naming system | `J = Unit` is the easy mathematical instantiation, and `named` is exactly the image of the partial `Option` assignment. The checked conclusion is still equality to `volume univ`, not to `1`. |
| Named image is countable | `D5.S0.Naming.named_countable (system : NamingSystem X) : system.named.Countable`. |
| Atomlessness makes the named image null | `Set.Countable.measure_zero`; the carrier theorem exposes the resulting equality as its second conjunct. |
| `mu(A(N)) = 1` | Missing checked bridge. The third conjunct is only `volume named_complement = volume univ`; no addressable probability specialization turns its right side into `1`. |
| Countable expansion tower | `J = Nat` is the easy mathematical instantiation. It proves the union of the family of named sets countable and null. |
| Nestedness and compatible extension | The union theorem does not need these hypotheses, but it also does not define an expansion relation, compatible assignments, or a limit `NamingSystem`. Their absence cannot be called strengthening until a checked limit construction connects the source carrier to the family union. |
| Limit anonymous set is full measure | Missing checked bridge. No declaration defines the limit system or proves `named(limit systems) = Set.iUnion fun k => (systems k).named`; the family-union complement is therefore not formally identified with the source's limit anonymous set. |

The dropped-or-weakened set is nonempty: the numeric probability specialization
and the tower-to-limit-system carrier identification are absent. `J = Unit` and
`J = Nat` demonstrate that the remaining mathematics is elementary, but they
are not checked, addressable discharges of those two clauses.

## Proof dependency trace

The exact repository dependencies are:

```lean
theorem name_layer_finite (system : NamingSystem X) :
    Countable system.Name

theorem named_countable (system : NamingSystem X) :
    system.named.Countable

theorem dark_side_conservation
    {X : Type u} [MeasureSpace X] [Uncountable X]
    [NoAtoms (volume : Measure X)] [SigmaFinite (volume : Measure X)]
    {J : Type w} [Countable J] (systems : J -> NamingSystem X) :
    volume (Set.iUnion fun j => (systems j).named) = 0
```

`name_layer_finite` uses `Set.countable_iUnion` over finite height layers;
`named_countable` uses `Set.countable_range` and injectivity of `Option.some`;
`dark_side_conservation` uses the pinned mathlib theorem:

```lean
theorem Set.Countable.measure_zero (h : s.Countable) (mu : Measure alpha)
    [NoAtoms mu] : mu s = 0
```

The full-measure conjunct then uses pinned mathlib:

```lean
lemma measure_of_measure_compl_eq_zero (hs : mu sᶜ = 0) :
    mu s = mu Set.univ
```

These are exact applications, not declaration-name similarity.

## Distinctness and prior coverage

Current-tree exact-ID searches over `docs/reports`,
`Meta/Digestion/formalizations`, `Golden/Frozen`, `D5`, `Blueprint`, and
`Evidence` returned no hit for the selected `9ba51e...` atom. Likewise:

```sh
git log --all --format='%H %s' \
  -S'pzg-residual-9ba51e073a6b7bfd395328fa2968c377a5539d3df64ffcd36797cf9a7faa3548' \
  -- docs/reports Meta/Digestion/formalizations \
     Golden/Frozen/accepted D5 Blueprint Evidence
```

returned no hit. The selected atom therefore has no prior report, receipt, or
atom-specific formalization in current-tree or all-reference history.

There is relevant cross-atom carrier coverage. Receipt
`Meta/Digestion/formalizations/pzg-residual-51fc797a08995981cd55c93a1b87c96aa5d79bc953ab471734c59a0ed6e8fa54.v1.json`
already binds the same frozen GID to `corollary/3.3.1`. Its authoritative atom
is only the narrative restatement that countable naming towers leave full
measure anonymous. The selected `theorem/3.3` additionally contains the
single-system clause and the countable-image proof. The atom is distinct, but
the shared GID is not mechanically reusable by the current cover command.

Static inspection of the live cover implementation exposes two independent
mechanical blockers. The primary gate is in `CoverAtomCommand.cs`: it computes
all baseline-bound GIDs before considering the legacy shared-residual path and
rejects an added GID already present there:

```csharp
var baselineGids = BaselineCoverageGids(baselineDocument);
if (addedGids.FirstOrDefault(baselineGids.Contains) is { } baselineConflict)
{
    throw new InvalidOperationException(
        $"cover GID {baselineConflict} is already bound in the baseline ledger");
}
```

The proposed GID is already baseline-bound by the `corollary/3.3.1` receipt, so
this gate would reject it before the cross-atom host checks run.

Independently, the current target ledger entry has `coverage_gids: []` and
`ast_path: theorem/3.3`; the existing host has
`ast_path: corollary/3.3.1`. Even absent the earlier baseline-GID rejection, the
hosted-extension guard in `CoverAtomCommand.HostedExtension.cs` is:

```csharp
if (target.CoverageGids.Length == 0
    || !string.Equals(target.AstPath, conflict.AstPath, StringComparison.Ordinal))
{
    throw CrossAtomBinding(gid, conflict.AtomId);
}
```

Both conditions in this independent guard reject the proposed relationship, so
the narrow legacy shared-residual exception cannot apply across these two AST
paths. `make cover` was not run; these conclusions come from the current ledger
values and the inspected ordering and predicates of the live implementation,
not from an invented command diagnostic.

## Search trace and decision

Focused searches found the exact carrier before any proof work:

```sh
rg -n -i 'countable|measure zero|MeasureTheory|Set\.range' D5 -g '*.lean'
rg -n 'Set\.Countable|measure_zero|measure.*countable' \
  .lake/packages/mathlib/Mathlib -g '*.lean'
rg -n -C 15 '定理 3\.3|常道守恒|命名系统|匿名集|扩张塔' \
  docs/develop/theory/INTERFACE_PHILOSOPHY.md
```

Relevant exact hits were `NamingSystem.lean`,
`NamingTowerConservation.lean`, mathlib `NoAtoms.lean`, and mathlib
`NullMeasurable.lean`. A third-party Lean ecosystem search was not run. Search
for an external declaration supplying either the probability specialization or
the compatible-tower limit-system bridge is therefore incomplete; this is
additional `open` evidence, not a nonexistence claim.

Decision: the atom remains operationally `open`. The existing theorem is a
substantive partial carrier, but no executable closure path currently exists:
it lacks the probability and limit-system bridges, and canonical cover rejects
cross-atom reuse of the already-bound GID. Any future mechanism permitting a
different cross-atom relationship is separately governed harness capability;
this report neither proposes nor implements such a change. This lane must not
create a second Lean source of truth or hand-edit receipt/frozen ledgers.

## Fidelity and non-hollowness checklist

- **Conclusion substance:** the frozen countable-family theorem is substantive:
  it proves countability, nullity, and complement measure equal to total measure.
  It is not `True`, definitionally `True`, or a restated hypothesis. It is only a
  partial carrier for the authoritative atom.
- **Hypothesis satisfiability:** no source-faithful candidate declaration or
  signature was produced. Consequently no candidate hypothesis witness was
  formed or checked; the probability and compatible-limit carrier needed for
  such a signature remain missing.
- **Domain inhabitance:** no source-faithful combined candidate domain was
  defined. `J = Unit` and `J = Nat` inhabit the frozen theorem's index domain,
  but they do not inhabit or construct the source's compatible expansion tower
  and its limit `NamingSystem`.
- **Proof substance:** the reusable theorem rests on the addressable countability
  and atomless-measure lemmas traced above. Reapplying it cannot manufacture the
  two missing bridges: `volume univ = 1` under an explicit probability instance,
  and `named(limit systems) = iUnion fun k => (systems k).named`.
- **Duplicate search:** the exact current-tree and all-reference atom-ID searches
  found no prior formalization of this atom. The one same-GID receipt is explicitly
  accounted for as distinct `corollary/3.3.1` coverage, not hidden as a duplicate.
- **Clause fidelity:** the dropped-or-weakened set for the frozen partial carrier
  is nonempty. The numeric probability specialization and tower-to-limit-system
  identification are absent, so deposit and cover are blocked.
- **Rendered-statement fidelity:** not run. No Lean/Scribe candidate or emitted
  statement was created, so there is no candidate rendering to compare.

No unavailable item is passed as verified or replaced by
`ASSUMED-UNVERIFIED`; the unavailable candidate checks force the `open` outcome.

## Grader-trap checklist

- **Generic vs specialized measure:** equality to `volume univ` is not the
  source's numeric equality to `1` without a checked probability specialization.
- **Family union vs limit object:** the complement of the union of named sets is
  not definitionally the anonymous set of a limit `NamingSystem`; a limit
  construction and named-set identity are required.
- **Easy instance vs addressable discharge:** choosing `J = Unit` or `J = Nat`
  is mathematical guidance, not a checked theorem carrying the omitted bridges.
- **Stronger theorem vs missing carrier:** dropping compatibility hypotheses can
  be a strengthening only after a checked map identifies the source limit
  carrier with the theorem's family union.
- **Cross-atom reuse vs canonical closure:** theorem relevance does not authorize
  ledger reuse. The baseline-GID gate rejects first, and the empty-target/AST
  hosted-extension predicates independently reject the proposed relationship.
- **Static analysis vs executed result:** no exact `make cover` error is claimed;
  the mechanical blocker is established from the live guard order and ledger
  values while the command remains unrun.

Verification reached in this lane:

- `make dotnet`: exit `0`, zero warnings and errors.
- Post-merge scoped
  `lake build D5.S0.Naming.Conservation.NamingTowerConservation`: exit `0`;
  Lean reported `Build completed successfully (2441 jobs)`. This command printed
  no axiom diagnostics.
- Historical pre-merge `make lean-report`: exit `0`; report SHA-256
  `bd7a5210d459c3a5fd8af2e051888c3695ffa1c72f6e456e6b6b8822ffa63be2`.
- Historical pre-merge `digest-status --formalize-candidates`: exit `0`; 137
  candidates; snapshot SHA-256
  `b5e23ac94a0aed91fb5fdc655f651eccd8731186c3a51c5077dc9683b9717316`.
- Selected `make show-atom`: exit `0`, all hashes matched.
- No deposit, cover, preflight, push, or PR was run. The two fidelity gaps and
  the live cover gates block executable closure.
- Post-merge base: `origin/dev` at
  `7535775879d67b7f2f46ea890942c2abf845d8da`; normal merge head before this
  follow-up report commit was
  `e18bf01cfae582ad089eb8b64a421be59f60effd`.
- Post-merge `git merge-base --is-ancestor origin/dev HEAD`: exit `0`.
- Post-merge `git diff --check`: exit `0`; the lane-specific diff against
  `origin/dev` contained only this report path.
