# Diagnostic Month R4 Lane B: Interface Theorem 3.3 Bind Recommendation

Outcome: complete bind recommendation to an existing frozen theorem. No new
Lean declaration, Scribe source, deposit, cover, receipt, or protected-ledger
edit was made. The remaining action is dispatcher-owned ledger binding.

## Baseline and atom

- Lane: `harness/diag-month-r4-b` at
  `/Users/mstudio3/trureturing-diag-month-r4-b`.
- Current base: `470491ca088663eeebf36415db7f65af3dc415ec`;
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

## Exact carrier

Bind to the already frozen declaration

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

The current raw Lean report records `kind=theorem` and exactly the standard
axiom closure `{Classical.choice, Quot.sound, propext}`. Freeze event
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

The source's Polish probability carrier is stronger than the Lean theorem's
measure assumptions: probability implies sigma-finiteness, its stated
atomlessness supplies `NoAtoms`, and an atomless Borel probability space cannot
have a countable carrier. The frozen theorem carries the resulting
`Uncountable X` fact as an explicit (proof-redundant) instance. The source's
countable names are represented by finite height sublevels;
`name_layer_finite` derives `Countable system.Name`. The generic
frozen conclusion deliberately says `volume complement = volume univ`; after
specializing to the source's probability measure, `volume univ = 1` gives the
source's numeric equality. The generic statement does not claim that arbitrary
non-probability measures have total mass one.

## Clause echo

| Source obligation | Exact formal discharge |
|---|---|
| Arbitrary naming system | Instantiate the carrier theorem with `J = Unit` and the constant singleton family. `named` is exactly the image of the partial `Option` assignment. |
| Named image is countable | `D5.S0.Naming.named_countable (system : NamingSystem X) : system.named.Countable`. |
| Atomlessness makes the named image null | `Set.Countable.measure_zero`; the carrier theorem exposes the resulting equality as its second conjunct. |
| `mu(A(N)) = 1` | The third conjunct is `volume named_complement = volume univ`; under the source probability measure, `volume univ = 1`. |
| Countable expansion tower | Instantiate `J = Nat` and `systems k = N_k`. The theorem proves the union of all named sets countable and null. |
| Nestedness and compatible extension | These hypotheses are not needed: the frozen theorem proves the conclusion for every countable family, strictly strengthening the source. A nested compatible tower is a special case, so no clause is dropped. |
| Limit anonymous set is full measure | The third conjunct applied to the `Nat` family is exactly the complement of the union of all tower-named points having the measure of the whole carrier. |

Thus the dropped-or-weakened set is empty. The lack of explicit nesting and
compatibility binders is strengthening, not omission: the proof does not use
them because countability alone suffices.

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

Current-tree exact-ID searches over `docs/devloop/reports`,
`Meta/Digestion/formalizations`, `Golden/Frozen`, `D5`, `Blueprint`, and
`Evidence` returned no hit for the selected `9ba51e...` atom. Likewise:

```sh
git log --all --format='%H %s' \
  -S'pzg-residual-9ba51e073a6b7bfd395328fa2968c377a5539d3df64ffcd36797cf9a7faa3548' \
  -- docs/devloop/reports Meta/Digestion/formalizations \
     Golden/Frozen/accepted D5 Blueprint Evidence
```

returned no hit. The selected atom therefore has no prior report, receipt, or
atom-specific formalization in current-tree or all-reference history.

There is intentional cross-atom carrier reuse. Receipt
`Meta/Digestion/formalizations/pzg-residual-51fc797a08995981cd55c93a1b87c96aa5d79bc953ab471734c59a0ed6e8fa54.v1.json`
already binds the same frozen GID to `corollary/3.3.1`. Its authoritative atom
is only the narrative restatement that countable naming towers leave full
measure anonymous. The selected `theorem/3.3` additionally contains the
single-system clause and the countable-image proof. This is not an exact atom
duplicate: it is a distinct atom reusing a theorem strong enough for both.

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
`NullMeasurable.lean`. No third-party search was needed after the exact pinned
carrier and its complete dependency path were established.

Recommendation: the dispatcher should bind atom
`pzg-residual-9ba51e073a6b7bfd395328fa2968c377a5539d3df64ffcd36797cf9a7faa3548`
to GID
`D5/S0/Naming/Conservation/NamingTowerConservation.countable_tower_anonymous_full_measure`
through the canonical ledger door. This lane must not create a second Lean
source of truth or hand-edit the receipt/frozen ledgers.

Verification reached in this lane:

- `make dotnet`: exit `0`, zero warnings and errors.
- `make lean-report`: exit `0`; report SHA-256
  `bd7a5210d459c3a5fd8af2e051888c3695ffa1c72f6e456e6b6b8822ffa63be2`.
- Current-base `digest-status --formalize-candidates`: exit `0`; 137 candidates;
  snapshot SHA-256
  `b5e23ac94a0aed91fb5fdc655f651eccd8731186c3a51c5077dc9683b9717316`.
- Selected `make show-atom`: exit `0`, all hashes matched.
- No deposit, cover, preflight, push, or PR was run because no new theorem is
  warranted and cross-review precedes dispatcher-owned binding.
