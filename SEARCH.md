# Formalization Search Receipt

Date: 2026-08-27

Atom:
`generic-residual-2bac7a2f727ce7146ebfb0dbece76b5c470eda4318a510300b3ebf83944ecf5b-4e5dbf9d334c265379a11b785c89b46079775ac7579b39e893f54b25d3ebaf2a`

Source CAS: `Meta/Digestion/atoms/sha256/2bac7a2f727ce7146ebfb0dbece76b5c470eda4318a510300b3ebf83944ecf5b`
(138 bytes, SHA-256 matches the filename).

## Ordered Due Diligence

1. Repository declarations (`D5/`): exact prior coverage found.

   - Searched declaration names and bodies for `card_pi`, policy sections,
     legal-action fibers, dependent products, and section cardinalities.
   - Exact hit:
     `D5/S3/ConceptDynamics/Agency/FinitePolicySectionCount.lean`, declaration
     `finite_policy_sections_card`.
   - The declaration constructs the source's total legal-action space from
     `Legal`, counts genuine sections of its first projection, and states the
     requested product equality.
   - Its Scribe already exists at
     `Blueprint/D5/S3/ConceptDynamics/Agency/FinitePolicySectionCount.scribe.cs`
     and its formula has the same section type, equality, and fiber product.
   - The 195-byte parent atom at
     `Meta/Digestion/atoms/sha256/c43c5686ddb89aae776fbc736f3dbb4dd4e1505ce20131bae7590eb9411a9c41`
     is exactly the 138-byte CAS plus the non-mathematical status sentence. It
     is already formalized to the exact hit above and frozen by repository
     history (`ea242d891`, `6613e57ff`).
   - Related but not primary hits:
     `Agency/DeterministicPolicyProductCount` exposes both the section-choice
     bijection and the same count, while
     `Policy/DeterministicPolicySectionCount` proves the later exponential
     lower-bound corollary.

   Conclusion: the atom is already covered by another module. Creating a new
   theorem, even as a wrapper with the same public type, would duplicate an
   existing truth source and violate the task's reverse-coverage rule.

2. Pinned Mathlib (`v4.31.0`, commit
   `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`): exact counting lemma found.

   - Local source search found `Nat.card_pi` in
     `Mathlib.SetTheory.Cardinal.Finite`:
     `Nat.card (forall a, beta a) = prod a, Nat.card (beta a)` for a finite
     index type.
   - It also found `Fintype.card_pi` and `Fintype.card_piFinset` in
     `Mathlib.Data.Fintype.BigOperators`.
   - Loogle query
     `Nat.card (forall a, ?beta a) = prod a, Nat.card (?beta a)` returned the
     single pattern match `Nat.card_pi` in the same module.
   - The existing D5 theorem directly uses `Nat.card_congr` for the honest
     section/dependent-product equivalence and then `Nat.card_pi`; there is no
     local reproof of the library cardinality theorem.

3. Third-party Lean ecosystem: no more specific section theorem found.

   - GitHub code search for `Nat.card_pi language:Lean` found direct reuse in
     TauCeti, Matroid, lean-iwasawa, gq2-lean, and COLT83, but no canonical
     legal-action projection-section declaration that supersedes the exact D5
     hit.
   - Reservoir package search for `card_pi` returned registry package results,
     not a theorem-level exact match.
   - An initial LeanSearch GET against `/api/search` returned HTTP 404. Reading
     the pinned `LeanSearchClient` exposed the correct POST `/search` protocol;
     the corrected query returned `Finset.card_pi`, `Fintype.card_pi`,
     `Fintype.card_piFinset`, and `Nat.card_pi` as its first exact candidates.

4. Local proof requirement: none. Mathlib supplies dependent-product counting;
   the exact existing D5 module already supplies the only source-specific step,
   namely the equivalence between projection sections and fiber choices.

## Premise Provenance

- `Legal : Q -> A -> Prop`: source section 54 defines
  `Legal : Q × A -> Prop` and the fiber
  `A(q) = {a in A : Legal(q,a)}` (source lines 3311-3322).
- `[Fintype Q]`: the standing hypothesis immediately before theorem 55.1 says
  that `Q` is finite (source line 3417). Proposition 76.1 restates the same
  finite-fiber count.
- No nonempty-fiber premise appears in the public theorem. This is deliberate,
  not a missing source condition: if one fiber is empty, the section type is
  empty and the product has a zero factor, so both cardinalities are zero.
  The task brief explicitly requires omitting this premise in that case.
- No finite-action or finite-fiber premise appears either. `Nat.card_pi` proves
  the equality for arbitrary fibers over finite `Q`; this is a strengthening
  of the finite-fiber source case and adds no premise.

## Faithfulness Probes

Reverse probe (the public theorem yields a nontrivial concrete consequence):

```lean
example :
    Nat.card
        {policy : Bool -> {qa : Bool × Fin 2 // True} //
          forall q, (policy q).1.1 = q} = 4 := by
  rw [finite_policy_sections_card (fun _ _ => True)]
  norm_num [Nat.card_eq_fintype_card]
```

There are two states and two legal actions in each fiber, so the theorem gives
`2 * 2 = 4` genuine projection sections. This checks that the public statement
counts the source's sections rather than an unrelated constant or empty type.

Trivialization probe:

```lean
example :
    Nat.card
        {policy : Unit -> {qa : Unit × Empty // False} //
          forall q, (policy q).1.1 = q} =
      ∏ _q : Unit, Nat.card {action : Empty // False} :=
  finite_policy_sections_card (Q := Unit) (A := Empty)
    (fun (_ : Unit) (_ : Empty) => False)
```

The type remains true with an empty fiber: both sides are zero. This is the
expected boundary behavior of a cardinality identity, not existential
hollowness. Therefore adding fiber nonemptiness would be an extra assumption.
The source's nonempty condition matters for existence of a policy, discussed
separately in the source, but not for this counting equality.

Both examples were compiled together in a temporary, subsequently removed
probe module using `make lean`. The first run failed because `decide` did not
reduce `Nat.card` and the empty-fiber call left type metavariables unresolved;
the corrected code above used `norm_num` and explicit `Q`/`A` parameters. The
corrected probe run ended with `EXIT=0`; receipts are `lean-probe.log`,
`lean-probe-rerun.log`, and `lean-probe-rerun-2.log` in the worker attempt
directory.

## Capacity Receipt

Before considering a target, `D5/S3/ConceptDynamics/Agency/` contained 9 files
and `D5/S3/ConceptDynamics/Policy/` contained 7 files, both below the SL-003
admission threshold of 12. No target was selected because exact prior coverage
made a new module inadmissible on single-source grounds.
