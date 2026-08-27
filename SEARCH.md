# Formalization search receipt

Atom: `generic-residual-f341c480522e5f9ba7480e0592071e1a9f71f77e3bd3f2ddde097d190e9ab2b3-a9273efbcceff28815f312702c4b9a439ca9d3ae9d021aa651acbbe2eaba80b7`

Source: `docs/develop/theory/FORMAL_OBSERVER_COMPLETION_REFLECTION.md`,
`命题/76.2/clause/1`.

## Statement echo and exact owner

The source defines the groupoid of all nonempty finite sets and bijections in
section 56. It asks for one element `c_S` of every such set and the transport
law `f (c_S) = c_T` for every bijection `f : S ≃ T`, then proves the family
does not exist using the swap of `{0, 1}`. Proposition 76.2 repeats that exact
no-go statement and names the same two-element swap proof.

The repository already has the exact public theorem and Scribe owner:

- Lean: `D5/S3/ConceptDynamics/Attribution/NoNaturalFiniteChoice.lean`
- declaration: `D5/S3/ConceptDynamics/Attribution/NoNaturalFiniteChoice.no_natural_finite_choice`
- Scribe: `Blueprint/D5/S3/ConceptDynamics/Attribution/NoNaturalFiniteChoice.scribe.cs`

Its type is:

```lean
¬ ∃ (choice : ∀ (α : Type) (_ : Fintype α) (_ : Nonempty α), α),
  ∀ (α β : Type) (fα : Fintype α) (fβ : Fintype β)
    (hα : Nonempty α) (hβ : Nonempty β) (e : α ≃ β),
      e (choice α fα hα) = choice β fβ hβ
```

This is clause-for-clause faithful:

- "deterministic choice element" is the single output in `α` of `choice`;
- "all nonempty finite sets" is the dependent quantification over every
  carrier `α` with `Fintype α` and `Nonempty α`;
- "natural under bijections" is the universal quantification over
  `e : α ≃ β` followed by the transport equality;
- "does not exist" is the outer `¬ ∃` over one global family, before all of
  the naturality quantifiers.

There are no extra theorem premises. `Fintype`, `Nonempty`, and `Equiv` are the
three object/morphism restrictions stated at source lines 3473-3507; the
nonexistence and swap proof are at lines 3510-3536 and are repeated at lines
5295-5299.

The digestion records independently confirm reuse. The source's theorem 56.1
atom `generic-residual-ad58375ebffa70799ce7508721046170dfa4ef2132e0455bba3e0e92e6fdc8dd`
is `absorbed-closed` by this GID. The proposition 76.2 parent atom
`generic-residual-334a6b2ab930a380d8c8768cb49eee1304d5d150357bc108c0928810d4c65553`
already has a precommitted signature with the same declaration name and type.
Therefore a wrapper theorem or second Scribe would duplicate an existing
truth owner. This implementation reuses the owner unchanged; the requested
stage also forbids the only remaining operation, depositing the child atom's
coverage receipt.

The canonical owner directory contains 6 Lean files (`ls
D5/S3/ConceptDynamics/Attribution | wc -l` also reports 6 entries), below the
SL-003 admission threshold of 12. No new address was allocated because the
canonical GID already exists.

## Ordered library search

1. Repository `D5/`: searches for `natural choice`, `natural selector`,
   `choice.*equiv`, and `selector.*equiv` found the exact theorem above.
   Related, more general action-level obstructions are
   `StabilizerSelectorObstruction.no_equivariant_selector_of_stabilizer_without_fixed_action`
   and `FixedSymmetrySelectorObstruction.no_equivariant_selector_of_common_fixed_symmetry`,
   but the exact finite-carrier owner takes precedence.
2. Pinned Mathlib: source searches for `natural.*(choice|selector)`,
   `choice.*bijection`, and `equivariant.*selector` found no packaged no-go
   theorem. Mathlib does supply the proof primitives used by the owner:
   `Equiv.swap` and its application lemmas in
   `Mathlib/Logic/Equiv/Basic.lean:636-712`, plus the `Fin 2` elimination
   principle used in the proof.
3. Third-party Lean ecosystem: Loogle query `"no natural finite choice"`
   returned `count: 0`; the structural query
   `Equiv ?e (?choice ?α) = ?choice ?β` also returned zero matches. GitHub code
   search for `"no_natural_finite_choice" language:Lean` returned
   `total_count: 0`. The LeanSearch API request returned HTTP 404, so it is a
   capability failure and is not counted as a negative search result.
4. Local proof: not attempted. Step 1 is an exact repository hit, so proving
   or wrapping it again would violate reuse-before-build and one-name-one-address.

## Reverse probe

The following `example` was checked through `make lean` in a temporary module.
It derives the nontrivial operational consequence that every proposed global
selector fails the stated transport law somewhere:

```lean
example
    (choice : ∀ (α : Type) (_ : Fintype α) (_ : Nonempty α), α) :
    ¬ ∀ (α β : Type) (fα : Fintype α) (fβ : Fintype β)
      (hα : Nonempty α) (hβ : Nonempty β) (e : α ≃ β),
        e (choice α fα hα) = choice β fβ hβ := by
  intro naturality
  exact no_natural_finite_choice ⟨choice, naturality⟩
```

## Trivialization probe

Restricting the object class to the one-point carrier makes natural choice
possible:

```lean
example : ∃ choice : Unit, ∀ e : Equiv.Perm Unit, e choice = choice := by
  refine ⟨(), ?_⟩
  intro e
  exact Subsingleton.elim _ _
```

Thus the no-go theorem cannot be obtained from nonemptiness alone or from a
trivial carrier. Its public type quantifies over *all* finite nonempty
carriers, so it includes `Fin 2`; naturality also quantifies over the
fixed-point-free swap of that carrier. This is the nondegenerate obstruction
and it is present in the theorem type, not hidden in the proof body.

## Verification history

- A temporary module containing exactly the two examples above passed
  `make lean` with exit code 0 and was then deleted so it would not become a
  second formal owner.
- Final-tree `make lean` passed with exit code 0 (10850 jobs). Its cache
  receipt reported `status=present`, `method=none`,
  `project_olean_state=warm`, and `mathlib_olean_state=warm`.
- The first `make emit` returned exit code 2 because the raw Lean report was
  stale for current inputs. `make lean-report` then returned 0 and refreshed
  the canonical report. The second `make emit` returned 0 and reported
  `emitted: 0 changed blueprint(s)`, confirming the existing Scribe projection
  required no change.
- No `make deposit` command was run and no PR was opened.
