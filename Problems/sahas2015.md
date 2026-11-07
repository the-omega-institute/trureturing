---
slug: sahas2015
bibkey: sahasrabudhe2015constantadditive
doi: 10.5281/zenodo.10456215
url: https://math.colgate.edu/~integers/p30/p30.pdf
triage: theorem
motivation_gids:
  - D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism
---

# Universal-input morphisms and constant even additive complexity

## Problem

Julian Sahasrabudhe, *Sturmian Words and Constant Additive Complexity*, INTEGERS 15 (2015), A30, Section 5, printed p. 7, asks:

> Can a construction of this form be generalized to give constructions of words with fixed even complexity?

The construction immediately preceding the question concatenates every finite word on a finite alphabet, then applies a morphism. This dossier anchors exactly its registered universal-input finite-morphism reading in [#22635](https://github.com/the-omega-institute/trureturing/issues/22635): every finite nonempty source alphabet $A$, every $w : \mathbb N \to A$ containing every finite source word, every $\varphi : A \to \mathbb Z^*$, and every infinite concatenated output $y$ satisfy

$$\neg\exists k\in\mathbb N,\quad k>0\ \land\ \forall n>0,\quad |S_n(y)|=2k,$$

where $S_n(y)$ is the set of sums of contiguous length-$n$ factors at every natural starting position. Empty codewords are allowed; cumulative codeword boundaries are unbounded. This is a negative answer to the construction question and a proof of the registered obstruction, not a refutation of its Lean `claim`.

### Statement echo

| Source clause or explicit registered reading | Lean counterpart | Fidelity |
| --- | --- | --- |
| Enumerate all words of finite length and concatenate them | `UniversalInput w` | Every finite source list occurs contiguously; the theorem allows every ordering with that property. |
| A finite nonempty source alphabet | `α`, `[Fintype α]`, `[Nonempty α]` | Arbitrary finite carrier; source names are immaterial. |
| Apply a morphism | `φ : α → List ℤ` and `IsMorphicImage w φ y` | The output is specified at every cumulative codeword boundary. |
| Infinite output, allowing empty codewords | Initial boundary zero, monotonicity, length recurrence, unboundedness, and pointwise output agreement | These are the explicit preregistered interpretation of concatenation. |
| Sums of consecutive symbols | `factorSum` and `sumSet` | Zero-based starts, all starts, exactly $n$ summands. |
| Fixed even complexity | `additiveComplexity y n = 2 * k` for every positive $n$, with $k>0$ | `Set.ncard`; a positive value supplies finiteness where needed. |
| Can this construction produce such a word? | `result : claim` | Universal impossibility under the registered reading. |

`List.ofFn (wordFactor w n i)`, `α → List ℤ`, and `List.flatMap` express the factor, morphism and concatenation directly. No forwarding definitions replace them. The six public definitions mirror the binding conventions; the only public theorem is `result`. The module has generality `G`, utility `none`, and admission basis `open-problem-resolution (#22635; Proved)`.

## Motivation

The theorem separates the universal-input finite-morphism method from other constructions of fixed additive complexity. The source's displayed code produces odd complexity, whereas the obstruction excludes every positive constant even value for this method. It includes erasing morphisms whose cumulative boundaries remain unbounded.

## Gap

The mathematical gap is the obstruction for arbitrary finite codewords rather than the source's special two-letter-long images. The result uses a complete-image sum rigidity argument and a reflected factor-sum set with a unique fixed point. It makes no classification claim about odd-complexity morphisms or about other source languages.

## Route

Assume every positive-length complexity equals a positive constant $B$. The private kernel-checked helper `same_length_sum` proves that complete images of equal length have equal sums. Otherwise concatenations of powers of two such source words give $B+1$ distinct sums at one positive length, contradicting the bound $B$.

Let $d$ be the gcd of the codeword lengths and $M$ their sum. Unbounded boundaries ensure $d>0$, including when some lengths vanish. The private helpers `length_closure_iff` and `padding_length` use `FreeAddMonoid.mrange_lift` and `Nat.exists_mem_closure_of_ge` to obtain $C$ such that every multiple of $d$ at least $C$ is a complete-image length. Choose $n=d(C+2M+1)>0$ and a complete image $W$ of length $n$.

The private helper `bracket_factor` brackets every length-$n$ factor inside a complete image of length at most $n+2M$. Pad that complete image to length $2n$. A duplicated source word occurs by universality. In its image, the adjacent complementary length-$n$ window has sum $2\Sigma W-z$ whenever the original window has sum $z$. This is `complementary_factor`.

Thus $S_n(y)$ is closed under $z\mapsto2\Sigma W-z$ and contains $\Sigma W$. The private helper `symmetric_ncard_odd` applies `Equiv.Perm.card_fixedPoints_modEq` to this involution: its unique fixed point forces an odd cardinality. The public `result` contradicts $B=2k$.

## Falsifier

A finite nonempty alphabet, a source word containing every finite word, a finite integer codebook with an infinite output satisfying all five boundary clauses, and a positive $k$ with exactly $2k$ distinct sums at every positive length would contradict `result`. A sampled finite prefix or a source missing finite words does not meet these quantified hypotheses.

## Evidence

- Kernel theorem: `D5.S1.Words.Complexity.SahasrabudheEvenAdditiveComplexityMorphism.result` in `D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.lean`.
- Canonical mirror: `Blueprint/D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.scribe.cs`; its settling node displays the whole proposition and carries one `OpenProblemResolutionClaim` of kind `Proved` for `sahas2015`.
- Frozen membership: `Golden/Frozen/state/D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism.lean.json`; it supplies the module statement identity, while declaration identities come from the compiled Lean report.
- Source: [Library note](../Library/Automata/sahasrabudhe2015constantadditive.md), DOI [10.5281/zenodo.10456215](https://doi.org/10.5281/zenodo.10456215), journal PDF above. No arXiv identifier is asserted.
- Escape audit unfinished for the sole public theorem: [#23244](https://github.com/the-omega-institute/trureturing/issues/23244). No typed registration is retained. A faithful dependent-family reconstruction, lawful template readout, equivalence bridge, variation/sensitivity and observational dependence remain missing; this is not `declared_validated`.

### Exact finite experiment

[Experiment directory at immutable revision `e54bc2be9b628087de72d10e740d6afc3089e25f`](https://github.com/the-omega-institute/trureturing-experiments/tree/e54bc2be9b628087de72d10e740d6afc3089e25f/docs/reports/sahasrabudhe-even-additive-complexity-morphism), script `check.py`, SHA-256 `ffad607841a6992894f66266b4d37a76f694157713bf6b2a2716cb5c20994a35`.

Git-object existence and the script hash are verified. The exact pinned script was run as `python3 /Users/auric/.sshx/f92cb825efcf0160162d045e/attempt-1/check-pinned.py`, exit 0, `ALL_CHECKS_OK`. For algebraic slopes $\sqrt2,\sqrt3$, it checks three distinct sums for each length 1–20 over starts 0–249. It also enumerates ordered pairs of nonempty codewords of lengths 1 or 2 over $\{-1,0,1\}$ having common slope, and checks reflection, the center and odd cardinality at admissible lengths 1–6 satisfying the script's conductor and gcd tests, using all binary source words of length $n+4$. The finite experiment does not cover empty codewords or arbitrary codebooks; those are covered by the quantified theorem.

## Triage

| Item | Status and evidence kind | Scope |
| --- | --- | --- |
| Empty codewords with unbounded boundaries | Proved; kernel-checked `result`, `bracket_factor` | The boundary model allows zero increments and requires unbounded output. |
| Equal-length complete images have equal sums; padding and duplicated words force odd cardinality | Proved; kernel-checked `same_length_sum`, `complementary_factor`, `symmetric_ncard_odd`, used by `result` | Under an assumed positive constant complexity; a positive complete-image length is constructed. |
| Pinned algebraic Sturmian and common-slope two-codeword checks | Computed; the exact experiment above, exit 0, `ALL_CHECKS_OK`, SHA-256 given above | Lengths 1–20 and starts 0–249 for Sturmian samples; nonempty codewords of lengths 1–2 over three integer letters, admissible lengths at most 6 for involutions. |
| Classification of all finite morphisms producing constant odd complexity | Open | No classification is asserted. |
| Other words realize every constant additive complexity $K>1$ | Proved externally; Sahasrabudhe (2015), Theorem 2; not formalized here | A different generalized-Sturmian input construction; the source theorem is compatible with `result`. |
| Other source factor languages | Open | Their replacement for universality and the corresponding obstruction remain unproved here. |

### What the settlement shows

The decisive mechanism is reflection of a finite sum set with one fixed point, obtained by sum rigidity and semigroup padding. The kernel-checked obstruction holds for arbitrary finite nonempty alphabets and erasing codebooks with unbounded boundaries, rather than only the source's particular code. It rules out one construction method, while the source's Theorem 2 and its generalized-Sturmian construction survive. The finite experiment checks its exact stated sample ranges only. A classification of odd-complexity morphisms and extensions beyond universal source languages remain open.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The source and adjacent-literature screen in #22635 covers the journal article, its identified citing papers, Banero's precursor, related additive-complexity work, author/title and question searches, MathOverflow and Zenodo; no settling result was found in that searched scope. This does not prove that no settlement exists elsewhere. The phrase “of this form” is interpreted by the explicit preregistered universal-input finite-morphism statement. The external Theorem 2 is cited as a published result, not as a theorem formalized in this module. Four-slot escape registration remains unfinished under #23244.
