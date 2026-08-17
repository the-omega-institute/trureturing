# Diagnostic Month R7 Lane A: Composite Cone Definition 10.1 Open Report

Outcome: `open` at the codex-formalize fidelity gate. Do not bind or cover this
atom with the existing `StrictChain` GID.

The dispatcher-assigned lane is
`/Users/mstudio3/trureturing-formalize-a-20260817` on branch
`harness/formalize-a-20260817`. Before this report was written, the clean lane
was fast-forwarded from `f403dc765267a50eb613ff65062a7fad5edf6bad` to the
then-current `origin/dev`, `2636b50795e599f73343f79be18f2d5398aa2bb0`.
`git merge-base --is-ancestor origin/dev HEAD` exited `0`.

No Lean, Blueprint, Scribe, digestion-ledger, frozen-ledger, formalization
receipt, or generated projection file was edited. The only intended change is
this report.

## Atom and authoritative statement

- Atom ID:
  `cone-residual-0f4325854c37465a2d844a3fa11941d067e6eb9e787f77dc171195d5818d5122`
- CAS reference:
  `sha256:0f4325854c37465a2d844a3fa11941d067e6eb9e787f77dc171195d5818d5122`
- Source ID: `cone-v1`; atomizer: `cone-v1`
- Source: `docs/develop/theory/CONE_PROGRAM_FORMAL.md`, `definition/10.1`
- Claim class: a definition clause with a strict-chain earning theorem

The authoritative command

```sh
make show-atom ATOM_ID=cone-residual-0f4325854c37465a2d844a3fa11941d067e6eb9e787f77dc171195d5818d5122
```

exited `0`. Raw, normalized, and CAS SHA-256 values matched. Its complete
mathematical text is:

```text
**定义 10.1。**复合系统三锥:SEP ⊂ PSD ⊂ SEP*(块正锥:⟨a⊗b|W|a⊗b⟩ ≥ 0 ∀a,b)。
```

Live `digest-status --json --base origin/dev` exited `0` and reported
`alignment=seen`, `migration=residual`, `truth=open`, `deletable=false`, with
the sole machine gap `coverage-gid-missing`.

The existing formalization receipt binds the atom to:

```text
D5/S3/Resource/CompositeCones/StrictChain.strict_composite_cone_chain_and_block_criterion
```

That receipt and the green compiler establish identity and proof validity, not
source fidelity. The producer-side fidelity gate below rejects the bind.

## Clause echo

| Authoritative clause | Candidate counterpart | Fidelity result |
|---|---|---|
| `SEP ⊂ PSD` | A proper inclusion for matrices on `Fin 2 × Fin 2`. | Narrowed from the unqualified composite-system definition to one two-qubit instance. |
| `PSD ⊂ SEP*` | A proper inclusion into repository `blockPositive`, again on `Fin 2 × Fin 2`. | Instance-only and the target predicate is broader than the conventional Hermitian block-positive cone. |
| `SEP*` is the block-positive cone | `blockPositive W` requires only nonnegative real parts of product-vector quadratic forms. | No Hermitian ambient restriction is present; the sets are not equal. |
| `⟨a⊗b|W|a⊗b⟩ ≥ 0 ∀a,b` | Universal `a,b`, `0 <= Re(dotProduct (star v) (W.mulVec v))`. | Lean carries conjugation, but the emitted formula drops `star` and renders `a × b`, not `a ⊗ b`. |

The dropped-or-weakened set is therefore nonempty. In particular,
instance-vs-general and pointwise-vs-operator fidelity both fail.

## Checked counterexample

The repository predicate admits a non-Hermitian matrix. This was checked in
the pinned toolchain with:

```sh
lake env lean /dev/stdin <<'EOF'
import D5.S3.Resource.CompositeCones

namespace D5.S3.Resource.CompositeCones

open scoped ComplexOrder

example :
    blockPositive
      (Complex.I •
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) := by
  intro a b
  let v : Fin 2 × Fin 2 → ℂ := fun ij => a ij.1 * b ij.2
  change 0 ≤ RCLike.re (dotProduct (star v) (Matrix.mulVec (Complex.I • 1) v))
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
  simp [smul_eq_mul, dotProduct, mul_comm]

example :
    ¬Matrix.IsHermitian
      (Complex.I •
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) := by
  intro h
  have hii := congrFun (congrFun h (0, 0)) (0, 0)
  have := congrArg Complex.im hii
  norm_num [Matrix.one_apply] at this

end D5.S3.Resource.CompositeCones
EOF
```

Exit code: `0`; stdout/stderr: empty.

Thus `i I` is accepted by the candidate `blockPositive` predicate but is not
Hermitian. It cannot be a member of the conventional Hermitian `SEP*` cone
named by the source definition. Compilation cannot repair this semantic gap.

## Artifact and rendering audit

`D5/S3/Resource/CompositeCones/StrictChain.lean` fixes both factors to
`Fin 2` and exposes the real-part predicate. Its header says `generality: G`,
although the codex-formalize taxonomy requires `I` for a concrete fixed
instance.

`Blueprint/D5/S3/Resource/CompositeCones/StrictChain.scribe.cs` renders the
product vector with `F.Times` and omits the Lean `star`. The emitted Markdown
therefore displays

```text
Re(dotProduct(a × b, W(a × b)))
```

instead of the source's bra-ket expression with tensor product and conjugate
bra. This is a symbol-level rendering mismatch, independently blocking cover.

## Search and verification

- `make -C tools dotnet`: exit `0`, zero warnings and zero errors.
- `make show-atom ATOM_ID=...`: exit `0`, all hashes matched.
- `lake build D5.S3.Resource.CompositeCones.StrictChain`: exit `0`; the named
  theorem has the expected std3 axiom closure.
- Repository search found no other complete strict-chain theorem.
- The frozen `CompositeCones` module supplies the general non-strict
  inclusions; `CompositeConeProperness` supplies two-qubit strictness witnesses.
  Neither removes the dimension or Hermitian gaps.
- The theorem conclusion is not `True`, not a hypothesis restatement, and has
  a checked matrix-domain inhabitant. Its two strictness witnesses make the
  proof substantive, but substance is not fidelity.

Grader traps:

- witness-vs-universal: pass
- instance-vs-general: fail
- conditional-vs-unconditional: pass
- pointwise-vs-operator: fail
- proof-internal-vs-addressable-statement: pass
- multi-clause residue names: pass
- mechanism-vs-outcome: pass

## Verdict

`OPEN` at codex-formalize Step 6. Do not run `make cover` for this atom/GID
pair. A faithful future closure needs an explicit dimension scope and an
independently anchored Hermitian block-positive carrier, followed by a Scribe
formula that preserves tensor-product and conjugate-bra semantics.
