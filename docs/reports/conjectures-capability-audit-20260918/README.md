# Conjectures.io as an Erdős capability benchmark

This report records a bounded audit made on 2026-09-18. It uses the public
[results page](https://conjectures.io/results), the site's
[verification description](https://conjectures.io/how-it-works), and the
public result records linked below. It is a capability and dependency audit,
not a claim that every public Erdős priority has been checked.

## What the site actually measures

The results page keeps four questions separate:

1. Is there a pinned Lean task with the intended statement and file set?
2. Did the submitted files pass the stated build and Lean-kernel checks?
3. Did a separate source and semantic review accept the scope and provenance?
4. What was the reward decision, and what exact result was credited?

At the time of this audit there were 32 unique result records: 27 Lean
verified and 5 Lean rejected. Of the verified records, 17 were review
approved, 5 received partial awards for task defects, and 5 were rejected in
review. These counts are records, not solved Erdős problems. A verified
record can be a refutation, a part, a variant, a duplicate, or a result whose
task had a defect. The site also exposes no reliable information about the
solver's private search process, so validator runtime is not evidence about
why a proof was found.

The accepted records show why their workflow is effective:

* The task is compact and its quantifiers are frozen before proof search.
* The proof closes the structural reduction and the final asymptotic
  quantifier; a stronger exact classification is not silently claimed.
* Finite combinatorial work is separated from the transfer to an infinite or
  asymptotic statement.
* Kernel verification, source review, and reward scope are reported as
  different facts.

The useful lesson for trureturing is therefore a dependency ledger for proof
obligations, rather than copying the site's theorem names or its reward count.

## Representative accepted obligations

### Erdős 272: an important exclusion for our target list

The [approved strong-variant record](https://conjectures.io/results/c3277f4a-d573-42a9-bfca-e45fb2cb39ff)
proves

$$
  N \mapsto \operatorname{maxArithInterCard}(N)-N^2/2=O(N)
$$

for the unrestricted family. The review records a structural reduction with
loss at most `2048 N` and a final coarse constant `30000`. It explicitly
does not prove an exact extremal formula or classify all extremal families by a
common point. The earlier common-point premise is discharged in the accepted
proof. Consequently this exact asymptotic target is prior evidence and must
not be selected again as a new solution target for trureturing.

The published source contains useful proof obligations such as private
witnesses, a shadow map, partial matching extension, and a finite upper-bound
to `O(N)` transfer. The source was inspected for declaration inventory and
architecture; it was not fully replayed in this checkout. These names are
evidence for candidate interfaces, not evidence that the corresponding
declarations are already frozen in D5.

### Erdős 108: a refutation is a result with a different scope

The [approved record](https://conjectures.io/results/8c083793-9c3c-4960-8a23-869e54fcb584)
constructs finite graphs of arbitrarily high chromatic number whose
girth-at-least-five subgraphs have chromatic number at most six. It refutes the
`r = 5`, `k = 7` universal instance and does not rely on an infinite-graph
convention. The upstream problem page still being labelled open does not make
this a new target. The proof is a deterministic graph construction, so it is
not evidence that a random-object/alteration theorem is missing from D5.

### Erdős 14(i): finite estimates must be connected to the target

The [approved part (i)](https://conjectures.io/results/dce3d778-6f52-4c27-8da0-c82d2f391b64)
proves a uniform finite lower bound for the number of exceptional two-term
representations, then transfers that bound to the all-`ε` asymptotic target.
Part (ii) is a separate reward target with shared proof material; it is not a
second independent demonstration of reuse.

### Erdős 196: a second bridge family

The [approved record](https://conjectures.io/results/e73b95f7-1d1b-42b5-a442-c07077741d73)
constructs a bijection of `ℕ` avoiding four-term arithmetic progressions in
both orientations. Its finite saturation and extension invariant is followed
by nested finite stages, eventual coverage, and the global limit object. This
is a reusable **finite-extension-to-infinite-object** pattern distinct from
an asymptotic estimate.

The [approved 18(b) record](https://conjectures.io/results/e93a2766-4c70-4564-b565-d0c556f35929)
also illustrates a completed internal transfer: a weighted dyadic mixing
premise is discharged inside the proof before the eventual `h(n!) < n^ε`
statement is claimed.

## Obligation classification for trureturing

The classification is per proof obligation. A whole accepted proof normally
contains all three classes at once.

| Obligation exposed by the records | Current evidence | Proper treatment |
| --- | --- | --- |
| Finite fibers, additive convolution, and additive energy | Pinned Mathlib contains `Finset.addConvolution`, `Finset.addEnergy`, the energy expansion, `card_sq_le_card_mul_addEnergy`, `le_card_add_mul_addEnergy`, and fiber-sum identities. | Register and use the upstream results. Do not add a theorem that only restates total mass, support, or a pointwise cap after summing fibers. |
| Hall matching, set-family shadows, LYM/Sperner, and compression | Mathlib contains finite Hall, shadows, LYM, and compression modules, including cardinality preservation and shadow monotonicity results. | Use these as library prerequisites. The #272-specific implication from private witnesses/slack to the Hall condition is a possible content theorem only when its exact hypotheses and a real consumer are fixed. |
| Finite counting to `O`, `o`, limits, or density | Mathlib supplies filters and asymptotic reasoning; the external FormalConjectures snapshot supplies `HasDensity` definitions and examples. The snapshot is not the project's pinned import surface, and some declarations are `proof_wanted`. | Audit each transfer at the exact quantifier level. Add a theorem only when a finite estimate yields a nontrivial new asymptotic conclusion not already in the pinned library. |
| Additive-basis language | The external snapshot defines `IsAddBasisOfOrder` and `IsAsymptoticAddBasisOfOrder` and uses them in Erdős tasks such as #326 and #881. | Treat this as upstream knowledge to be imported or registered after compatibility checking. It is not evidence that the project already has a proved additive-basis API. |
| Graph construction and invariant transport | Mathlib supplies `Colorable`, coloring pullback through graph homomorphisms, monotonicity, and unconditional extended-girth transport such as `egirth_anti` and `IsContained.egirth_le`. | Prove the operation-specific transport used by a construction (blow-up, product, arc graph, or subgraph), rather than wrapping a monotonicity theorem. |
| Random object to deterministic object | D5 already has finite Bonferroni, finite capture probabilities, and second-moment modules. Mathlib has the general probability and moment infrastructure. | Do not create a first-moment wrapper. A genuine alteration, second-moment, or local-lemma consumer must first identify a new conclusion and a live proof path. |
| Finite extension to a global object | #196 demonstrates the pattern; no general D5 declaration with the same stage-invariant and coverage quantifiers was identified in this bounded search. | Keep this as a candidate content bridge. It needs a second independent consumer before a broad abstraction is justified. |
| #272 local incidence → matching → shadow → extremal bound | The published proof exposes private-point and matching obligations. Our existing #272 report is explanatory material; the exact accepted declarations were not established as frozen D5 interfaces in this audit. | Preserve the report as a source map. Formalize only a non-bind-only structural implication, with a precise consumer and a dependency review. |

The boundary matters. During this audit an attempted theorem of the form

$$
  (\forall x, r_{A+B}(x)\le K)\Longrightarrow |A||B|\le K|A+B|
$$

was removed. Its proof is fiber counting, support restriction, and summation
normalization from existing results. Naming it does not create mathematical
content under the repository's bind-only rule.

## What the accepted proofs reveal about our missing bridge

The gap is not a single “Erdős library”. It is the seam between the strong
finite mechanisms already present in D5 and the target language used by the
problems:

1. **Structural incidence to a global extremal bound.** D5 can express finite
   counts and local witnesses, but the #272-style defect/slack statement that
   forces a Hall condition and then a shadow bound is a new mathematical
   obligation when its hypotheses are not already available.
2. **Finite estimate to asymptotic target.** Exact finite inequalities are
   common in our tree. We need explicit, reusable transfers for the actual
   domains, error terms, and filters appearing in consumers. A generic wrapper
   around `Tendsto` or `Big-O` is not enough.
3. **Stable finite stages to an infinite object.** The #196 proof shows that
   saturation, extension, prefix stability, and eventual coverage form a
   separate reusable interface. This is a better candidate than another
   Fibonacci-specific lemma, but only after a second consumer appears.
4. **Object operation to graph invariant.** The library has the invariant
   definitions and monotonicity laws; constructions still need their own
   homomorphism, girth, and coloring transport proofs.
5. **Probabilistic consumers.** D5 has moment calculations, so the next useful
   probability contribution must turn a particular random construction into an
   existence or alteration conclusion. The #108 record itself supplies no
   evidence for this route because it is deterministic.

These are bridges between interfaces, not renamed library definitions. A
candidate is worth formalizing when the statement survives inlining of all
existing prerequisites, is used on a live proof path, and has at least one
independent consumer. Repeated obligations across two different accepted
records are the benchmark's strongest signal.

## Target screen and current KPI

The target check was performed before selecting a new line:

* [Erdős #156](https://www.erdosproblems.com/forum/thread/156) remains open
  with zero dedicated proof claims and no current-worker marker on the problem
  page. Its exact unresolved statement is the maximal Sidon subset of
  `{1,…,N}` with size `O(N^(1/3))`; the known logarithmic construction does not
  settle it. The tracked attempt in issue [#8450](https://github.com/the-omega-institute/trureturing/issues/8450)
  returned no complete proof or counterexample, so the target stays open.
* [Erdős #734](https://www.erdosproblems.com/forum/thread/734) is open with no
  dedicated claim, but its current finite-field route lists thirteen explicit
  failure modes. It is a backup investigation, not a proof claim.
* #326 and #881 are excluded because their ordinary discussions contain
  complete-answer claims and active workers, despite zero dedicated claim-tab
  counts.
* #108 is excluded because the approved Conjectures.io refutation already
  covers the universal `r=5`, `k=7` instance. #845 is already marked
  disproved and is useful only as a benchmark.

The measurable benchmark outputs are: distinct records audited; obligations
classified; exact frozen reuse; pinned-upstream interfaces; repeated
unfilled obligations with at least two independent consumers; and complete
source-cleared Erdős resolutions. No coverage percentage is reported until
these sets are defined and measured against a fixed corpus.

**Complete Erdős solutions: 0.** This audit changes neither the KPI nor the
status of #156. It supplies a source and dependency map for the next proof
attempt.

## Limits of this audit

The result pages and a declaration inventory of the published Lean sources were
read, but the downloaded proof files were not all replayed in the project
checkout. External FormalConjectures declarations were checked for source
presence and were not treated as project capabilities. A missing name in a
text search is therefore not a proof of semantic absence; it is a reason to
run an exact import and type-check probe before opening a formalization task.
