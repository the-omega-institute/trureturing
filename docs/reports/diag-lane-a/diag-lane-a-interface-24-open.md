# Diagonal Lane A: Interface 2.4 Open Report

Outcome: open, with no formalization deposit.

This report records the evidence for the isolated lane
`harness/diag-lane-a-20260814` at
`/Users/mstudio3/trureturing-diag-lane-a-20260814`. The lane is based on
`origin/dev` at `c1a35d610368a7f83af7ec88308e0ab4737c0966`.

`git merge-base --is-ancestor origin/dev HEAD` exited `0`; the worktree was
clean before this report was added. No files under `Meta/Digestion/**`,
`Golden/Frozen/**`, or formalization receipts were edited.

## Atom and authoritative statement

- Atom ID: `pzg-residual-8f0ea7d802c3374e1e7e180343c936251b8488cd332a1354e226d484535ed16b`
- CAS reference: `sha256:8f0ea7d802c3374e1e7e180343c936251b8488cd332a1354e226d484535ed16b`
- Source: `docs/develop/theory/INTERFACE_PAPER.md`, `definition/2.4`
- `make show-atom ATOM_ID=pzg-residual-8f0ea7d802c3374e1e7e180343c936251b8488cd332a1354e226d484535ed16b` exited `0`.
- `show-atom` reported `status=match` for raw, normalized, and CAS SHA-256 values.

The authoritative text, copied from the successful `show-atom` output, is:

> **定义 2.4(自应用片段)。** 若另有有限集 A, Y,称映射 g: A → Y^A 为一张**清单**(A 中每名 a 命名一个函数 g(a): A → Y)。给定**扭** f: Y → Y,**对角构造**为 d_g ∈ Y^A,d_g(a) := f(g(a)(a))。称 g 被**逃逸**若 d_g ∉ g(A)。
>
> 此片段中 Lawvere 定理 [Law69] 的定性形式为:若 f 无不动点,则每张清单被逃逸(Cantor、Gödel、Tarski、Turing 论证之共同抽象)。下节将其定量化。

## Statement echo and existing coverage

The source clauses map one-to-one to already frozen repository machinery:

1. **Finite carriers and listing:** the finite carrier encoding is `[Fintype A] [Fintype Y]`; a listing `g : A → Y^A` is represented by the curried `g : A → A → Y` in `D5/S0/Diagonal/EscapeCount`.
2. **Twisted diagonal:** `D5.S0.Diagonal.EscapeCount.diagonal (f : Y → Y) (g : A → A → Y) : A → Y` is definitionally `fun a => f (g a a)`, matching `d_g(a) := f(g(a)(a))` after currying.
3. **Escape predicate:** `D5.S0.Diagonal.EscapeCount.IsEscaped f g` is `diagonal f g ∉ Set.range g`, matching `d_g ∉ g(A)`.
4. **Lawvere qualitative consequence:** `D5.S0.Diagonal.CaptureCount.escape_all_of_fixfree` proves
   `Nat.card {y : Y // f y = y} = 0 → ∀ g : A → A → Y, IsEscaped f g`.

The existing named declarations are:

- `D5/S0/Diagonal/EscapeCount.diagonal`
- `D5/S0/Diagonal/EscapeCount.IsEscaped`
- `D5/S0/Diagonal/EscapeCount.diagonal_landing_fixed`
- `D5/S0/Diagonal/EscapeCount.escaped_listing_card`
- `D5/S0/Diagonal/CaptureCount.escape_all_of_fixfree`

The source's next quantitative section is separately represented by the
already frozen `D5/S0/Diagonal/EscapeCount.escaped_listing_card` receipt for
atom `pzg-residual-c0a63f4cbbe848e456ae1f847150de6bf63e59a5295bf711230af4bbb4860cab`.
Creating a new module for definition 2.4 would therefore be a renamed
duplicate and would not add an independently addressable theorem. The
definition atom remains open in its ledger shard (`coverage_gids: []`) for the
dispatcher to bind or classify; this lane does not edit that ledger.

## Library search trace

The following searches were run in the synced worktree.

```text
rg -n "escapedListings|IsEscaped|diagonal_landing_fixed|escaped_listing_card|escape_all_of_fixfree" D5/S0 Blueprint/D5/S0 Meta/Digestion/formalizations --glob '*.lean' --glob '*.md' --glob '*.json'
```

Hits include the declarations listed above and their Blueprint mirrors. The
formalization receipts found were:

```text
pzg-residual-9d52e41b062f81b1ce93cf241bf4ef9806f6e6de3fe9d6d10b5dc2de6d1f929a.v1.json  D5/S0/Diagonal/EscapeCount.diagonal_landing_fixed
pzg-residual-c0a63f4cbbe848e456ae1f847150de6bf63e59a5295bf711230af4bbb4860cab.v1.json  D5/S0/Diagonal/EscapeCount.escaped_listing_card
pzg-residual-5182a7b237a49baa85ccb70a1989f2411de3b045e8461fe9359a15ab3789f0ab.v1.json  D5/S0/Diagonal/CaptureCount.capture_independent
```

```text
rg -n "lawvere|Lawvere|self.application|self-application|diagonal.*fixed|allListingsEscaped" D5/S0/Computability D5/S0/Diagonal Blueprint/D5/S0/Computability Blueprint/D5/S0/Diagonal --glob '*.lean' --glob '*.md'
```

This found the frozen diagonal count, fixed-point-free escape, and related
Lawvere modules; no separate missing carrier or alternate diagonal mechanism
was found.

```text
rg -n "pzg-residual-8f0ea7d802c3374e1e7e180343c936251b8488cd332a1354e226d484535ed16b" Meta/Digestion/backfill/interface-v1
```

This found the authoritative residual shard with `ast_path: definition/2.4`,
empty `coverage_gids`, and no existing receipt claiming this exact atom.

## Failed approaches and diagnostics

- **Create a fresh definition module:** rejected as a renamed duplicate. The
  exact diagonal and escape predicates already exist, and the Lawvere
  consequence is already named and proved by `escape_all_of_fixfree`.
- **Create a wrapper theorem with a new curried/uncurried spelling:** rejected;
  it would only repackage the same statement and leave no new mathematical
  content. The source's `Y^A` notation is represented by the existing curried
  function type without an additional theorem obligation.
- **Formalize only the first paragraph and ignore the Lawvere clause:**
  rejected by clause fidelity. The qualitative consequence is an independently
  testable claim and must remain in the atom's accounting.
- **`make dotnet`:** exited `0`; all projects built with zero warnings and zero
  errors.
- **`lake build D5.S0.Diagonal.CaptureCount`:** exited `0`; replayed 940 jobs
  and reported `Build completed successfully`. Lean emitted only the existing
  unused-`Fintype` linter warning for `escape_all_of_fixfree`.

## Fidelity gate

- Conclusion substance: satisfied by the existing named theorem; no new
  conclusion is introduced.
- Hypothesis satisfiability: witnessed by the compiling declaration
  `D5.S0.Diagonal.CaptureCount.escape_all_of_fixfree` and its `[Fintype A]
  [Fintype Y]` context; no new signature is proposed.
- Domain inhabitance: the existing theorem's finite function domain is the
  exact repository encoding; no new domain is introduced.
- Proof substance: already supplied by the nontrivial finite-cardinality and
  subtype argument in `EscapeCount`/`CaptureCount`.
- Deposit substance: blocked for a new module because all source vocabulary
  is connected to and already earned by the existing diagonal machinery.
- Duplicate search: complete; exact command traces and receipt GIDs are
  recorded above.
- Clause fidelity: complete for the open decision; all four definitional and
  qualitative clauses are mapped, with no dropped or weakened clause.
- Rendered-statement fidelity: existing Blueprint mirrors were inspected; no
  new Scribe artifact is created, so no new render can drift.
- Grader traps: witness-vs-universal and instance-vs-general do not arise;
  conditional-vs-unconditional is preserved by retaining the explicit
  fixed-point-free hypothesis; mechanism-vs-outcome is preserved by mapping
  both `diagonal` and `IsEscaped` to named definitions.

`make deposit`, `make preflight`, `make cover`, Lean inspector admission,
receipt emission, and coverage alignment were not run because the skill
requires stopping with `open` before deposit when the candidate would be a
duplicate. These are unreached classes, not claimed successes or failures.

## Lane state

The only intended worktree change is this report. No formalization artifact
exists, and no ledger or receipt file was modified. The dispatcher must decide
whether to bind this residual atom to the existing diagonal declarations or
leave it open as an already-covered duplicate.
