# Diagonal Lane A: Interface 3.7 Transitive Probability Open Report

Outcome: open; no formalization deposit.

This report records the diagnostic lane `harness/diag-lane-a-20260814` in
`/Users/mstudio3/trureturing-diag-lane-a-20260814`. The lane was aligned with
the fetched `origin/dev` at `0e23f3412a0cfd4d6b4865209097c7ad1e766d73` by
merge commit `58cff04b`; `git merge-base --is-ancestor origin/dev HEAD`
exited `0`. The two failed draft files were removed. No files under
`Meta/Digestion/**`, `Golden/Frozen/**`, or formalization receipts were edited.

## Atom and authoritative statement

- Atom: `pzg-residual-fb628b740c13155e81b509989a3d90fac9be23a0833932aceb0e866039f3a033`
- Source: `docs/develop/theory/INTERFACE_PAPER.md`, `theorem/3.7/occurrence/2`
- `make show-atom ATOM_ID=pzg-residual-fb628b740c13155e81b509989a3d90fac9be23a0833932aceb0e866039f3a033` exited `0`.
- The command reported `status=match` for raw, normalized, and CAS SHA-256 values.
- The selected ledger shard has `coverage_gids: []`, `receipts.coverage: []`,
  `receipts.scribe: []`, and no unresolved subitems.

One-to-one statement echo from the successful atom read:

> **定理 3.7(传递特例;一般版的单因子形)。** 若 G ≤ Sym(A) 传递，记 ω 为 Stab(a₀) 在 A 上之轨道数，则一般轨道连乘式只有一个因子:
> $$ P^{\mathrm{eq}}_{\mathrm{esc}} = 1 - \frac{k}{n^{\omega}} . $$
> *说明。* 这是定理 3.7 的传递特例，由轨道指标集为单点直接得到；正则 ℤ₃、正则 ℤ₄ 与非正则 S₃ 的三项实证保留为冗余核验。一般(含非传递)情形已由定理 3.7 的双射与条件启示证明闭合。

The source requires a probability identity for finite transitive actions,
not merely an escaped-listing cardinality.

## Existing machinery and coverage boundary

The frozen diagonal module `D5/S0/Diagonal/EquivariantEscape.lean` contains:

- `D5/S0/Diagonal/EquivariantEscape.equivariant_escaped_card`, the general
  orbit-product **count**;
- `D5/S0/Diagonal/EquivariantEscape.transitive_equivariant_escaped_card`, the
  transitive single-factor **count**;
- `D5/S0/Diagonal/EquivariantEscape.OrbitDecomposition`, an explicit bridge
  from equivariant listings to orbit coordinates and an escape-preservation
  witness.

The covered sibling atom is
`pzg-residual-0fc2fbafca1ca2eadda19220eb981830b2762bc0799edb3acabf8fc4d7a1fcb4`
(`theorem/3.7/occurrence/1`), whose receipt names
`equivariant_escaped_card`. `make show-atom` for that atom also exited `0` with
`status=match`; it is a different occurrence and does not close this residual.
The B-side candidate
`pzg-residual-c224075beaadf568f7b388e82d35d77de1f72418008e89d8ce4b0fca5534c101`
resolves to `pzg-v170`, `remark/27.164`, and is unrelated. The C-side candidate
`pzg-residual-c4dd0c241dbf2b9cb4e59dd55a1419404192fab2b6089fb1d3ee6ea020117a9a`
resolves to interface theorem 6.4 and is unrelated. These checks were made by
successful `make show-atom` calls with `status=match`.

The repository defines `escapeProbability` for unrestricted listings in
`D5/S0/Asymptotics/FixedPointFreeEscapeProbability.lean`; it does not define a
probability for the equivariant-listing subtype. Introducing a new normalized
probability definition would therefore add source machinery not explicitly
present in this atom. Also, the frozen count theorem takes an
`OrbitDecomposition` witness. The authoritative transitive statement assumes
only finite transitive group action data, so using that theorem directly would
silently strengthen the hypotheses. A generic decomposition theorem is not
available in the current frozen machinery.

Consequently, the existing count is relevant evidence but is not a faithful
formalization of the requested probability theorem. The correct disposition is
`open`, not deposit.

## Failed draft diagnostics

An attempted probability module and Scribe mirror were created only for
diagnosis and then deleted.

`lake build D5.S0.Asymptotics.EquivariantEscapeProbability` exited `1`. The
fresh build reported:

- a type mismatch while defining the local `OffDiagonalOrbit` alias;
- `Unknown identifier OffDiagonalOrbit` in the following declaration;
- missing `Nonempty Y` for the denominator positivity proof;
- unsolved real denominator/subtraction identity goals;
- unknown constant `Nat.card_subtype_le`;
- the theorem depended on `sorryAx`.

`make dotnet` exited `1` with:

```text
Blueprint/D5/S0/Asymptotics/EquivariantEscapeProbability.scribe.cs(36,12):
error CS1026: expected ')'
```

The Scribe draft also omitted the authoritative binders and hypotheses
(`G`, `A`, `Y`, `Group`, `MulAction`, `Fintype`, `Nonempty`, `Pretransitive`,
`D`, and `i₀`), so it could not pass rendered-statement fidelity even after a
syntax repair.

## Fidelity gate and lane disposition

- Conclusion substance: **not closed**; only the count is frozen.
- Hypotheses: the existing theorem requires the extra `OrbitDecomposition`
  witness, while the source states a finite transitive action directly.
- Probability normalization: **missing** for equivariant listings.
- Proof substance: the attempted Lean proof does not compile and carries
  `sorryAx`.
- Rendered-statement fidelity: failed; the Scribe draft does not parse and
  omits source binders.
- Duplicate and conflict search: complete; the exact occurrence/1 sibling is
  covered, while B and C candidates are unrelated.

No `make deposit`, `make preflight`, `make cover`, receipt emission, or
coverage alignment was run because the candidate is blocked at the open
diagnostic stage. The only report artifact added by this lane is this file.

