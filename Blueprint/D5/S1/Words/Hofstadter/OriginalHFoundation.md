# The original H and its morphic word

## Abstract

The original Hofstadter H is exactly the complement of the number of letters 1 in every prefix of the original ternary fixed word.

The cited source defines H(0)=0 and H(n+1)=n+1-H(H(H(n))). Its Theorem 3.1 and Proposition 4.1 relate it to the substitution 1 to 2, 2 to 3, and 3 to 31. The three nested applications, the initial value, the original letters and the initial letter 3 are retained here.

**Definition 1.1 (Original letters).**

Lean statement: `D5/S1/Words/Hofstadter/OriginalHFoundation.Letter`

*Formalization.* `D5/S1/Words/Hofstadter/OriginalHFoundation.Letter` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

Letter has exactly the three constructors one, two and three, representing the source labels 1, 2 and 3 in that order. These are letters, not values of H.

**Definition 1.2 (Original substitution).**

Lean statement: `D5/S1/Words/Hofstadter/OriginalHFoundation.tau`

*Formalization.* `D5/S1/Words/Hofstadter/OriginalHFoundation.tau` (`✓ std3`).

*Citation.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

tau maps one to the singleton two, two to the singleton three, and three to the two-letter list three, one. Its extension to finite words is the existing polymorphic substitution subst, which concatenates the letter images in order.

**Definition 1.3 (Literal iterates).**

Lean statement: `D5/S1/Words/Hofstadter/OriginalHFoundation.block`

*Formalization.* `D5/S1/Words/Hofstadter/OriginalHFoundation.block` (`✓ std3`).

*Citation.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

For every natural k, block k is the literal list tau iterated k times on the singleton three, using the existing polymorphic image operation. In particular block 0 is the singleton three.

**Definition 1.4 (All finite prefixes).**

Lean statement: `D5/S1/Words/Hofstadter/OriginalHFoundation.wordPrefix`

*Formalization.* `D5/S1/Words/Hofstadter/OriginalHFoundation.wordPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

For every infinite word x : Nat to Letter and natural n, wordPrefix x n is the list x(0),...,x(n-1), in increasing position order. Its length is n, and wordPrefix x 0 is empty.

**Definition 1.5 (Literal infinite fixed-word condition).**

Lean statement: `D5/S1/Words/Hofstadter/OriginalHFoundation.IsOriginalWord`

*Formalization.* `D5/S1/Words/Hofstadter/OriginalHFoundation.IsOriginalWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

For every x : Nat to Letter, IsOriginalWord x means both x(0)=three and the following condition for every natural n: subst tau (wordPrefix x n) equals wordPrefix x of length (subst tau (wordPrefix x n)).length. Thus the substitution of every finite prefix is the corresponding finite prefix of the same infinite word. No supplied infinite word is assumed to exist.

**Definition 1.6 (The constructed infinite word).**

Lean statement: `D5/S1/Words/Hofstadter/OriginalHFoundation.word`

*Formalization.* `D5/S1/Words/Hofstadter/OriginalHFoundation.word` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

For every natural n, word n is the letter at index n of block n, with three as the total default. The growth and agreement theorem ensures that this index is in range and that the default is never used. This construction uses only the original literal substitution iterates.

**Definition 1.7 (The original numerical equations).**

Lean statement: `D5/S1/Words/Hofstadter/OriginalHFoundation.IsOriginalH`

*Formalization.* `D5/S1/Words/Hofstadter/OriginalHFoundation.IsOriginalH` (`✓ std3`).

*Citation.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

For every f : Nat to Nat, IsOriginalH f means f(0)=0 and, for every natural n, f(n+1)=n+1-f(f(f(n))). All arguments and subtraction are natural numbers. There are exactly three nested applications.

**Definition 1.8 (Independent numerical realization).**

Lean statement: `D5/S1/Words/Hofstadter/OriginalHFoundation.H`

*Formalization.* `D5/S1/Words/Hofstadter/OriginalHFoundation.H` (`✓ std3`).

*Citation.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

For every natural n, H n is eval n n. The structurally recursive auxiliary eval has eval 0 m=0 and eval (p+1) m=m-eval p (eval p (eval p (m-1))). Each auxiliary value is at most its argument. The coherence proof shows that two depths p and q at least m give the same value at m. H is constructed independently of word and all letter counts.

**Definition 1.9 (Complementary prefix count).**

Lean statement: `D5/S1/Words/Hofstadter/OriginalHFoundation.positive`

*Formalization.* `D5/S1/Words/Hofstadter/OriginalHFoundation.positive` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

For every finite word w, positive w counts its letters different from one, using List.countP. Consequently positive w plus List.count one w equals the length of w.

**Theorem 1.10 (Existence and uniqueness of the original H).**

Lean statement: `D5/S1/Words/Hofstadter/OriginalHFoundation.h_characterization`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Hofstadter/OriginalHFoundation.h_characterization` (`✓ std3`). ∎

*Citation.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

The conjunction has two clauses: IsOriginalH H, and for every f : Nat to Nat, IsOriginalH f implies f=H. The first clause verifies both H(0)=0 and H(n+1)=n+1-H(H(H(n))) for every natural n. The second clause is equality of total functions, proved by strong induction using H(n) at most n at every nested argument. Thus the numerical equations have an actual, unique realization.

**Theorem 1.11 (Existence, uniqueness and arbitrary prefix coverage).**

Lean statement: `D5/S1/Words/Hofstadter/OriginalHFoundation.word_characterization`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Hofstadter/OriginalHFoundation.word_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

Four clauses hold simultaneously. First, IsOriginalWord word. Second, for every x : Nat to Letter, IsOriginalWord x implies x=word. Third, for every natural k, k+1 is at most the length of block k. Fourth, for all natural n and k, n at most the length of block k implies wordPrefix word n=(block k).take n. In particular all natural prefix lengths occur, and equality is allowed at every whole-block endpoint. The proof uses block(k+1)=block(k) followed by the nonempty k-th iterate of the letter one. Nesting and growth identify the finite iterates with the literal rooted infinite fixed word.

**Theorem 1.12 (Exact original prefix-count correspondence).**

Lean statement: `D5/S1/Words/Hofstadter/OriginalHFoundation.original_h_morphic_prefix`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Hofstadter/OriginalHFoundation.original_h_morphic_prefix` (`✓ std3`). ∎

*Citation.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

For every infinite word x : Nat to Letter, every proof hx of IsOriginalWord x, and every natural n, H(n)+List.count one (wordPrefix x n)=n. Equivalently H(n)=n-List.count one (wordPrefix x n). This includes n=0 and every whole-block endpoint, without a finite-horizon or a sufficiently-long-block premise. The word characterization supplies an actual x, and the numerical characterization identifies this H with every function satisfying the original triple recurrence.

To see the correspondence, write P(n) for positive(wordPrefix word n). For an arbitrary finite word w and natural cut n in its substituted word v, put r=positive(v.take n). The number of letters three in v.take n equals positive(w.take r), and the number of letters one in v.take(n+1) equals the number of letters three in w.take r. These identities hold also when a cut is inside the image 31, at a whole-block boundary, at zero, or beyond the finite word. They follow by splitting the three original letter images. Prefix agreement transfers them to P(P(n))=countThree(wordPrefix word n) and countOne(wordPrefix word(n+1))=countThree(wordPrefix word(P(n))). It follows that P(P(P(n)))=countOne(wordPrefix word(n+1)), and the complementary count gives the original triple recurrence for P. Numerical uniqueness then gives P=H.

The numerical characterization and prefix-count correspondence are known mathematical results. The canonical Library note supplies their precise locators and the author's public-domain Coq source. The numerical depth construction follows GenG.v; the arbitrary-cut counting argument proves the morphic bridge here. External source code supplies mathematical guidance; the Lean proofs establish the statements here. No mathematical novelty is asserted.

These statements concern exact natural-number values and word prefixes. They give no machine execution, input acquisition, serialization, bit-operation count, memory bound, frequency limit, or quantitative automaton lower bound.

## References

- Truth anchor: `D5/S1/Words/Hofstadter/OriginalHFoundation.H`
- Truth anchor: `D5/S1/Words/Hofstadter/OriginalHFoundation.IsOriginalH`
- Truth anchor: `D5/S1/Words/Hofstadter/OriginalHFoundation.IsOriginalWord`
- Truth anchor: `D5/S1/Words/Hofstadter/OriginalHFoundation.Letter`
- Truth anchor: `D5/S1/Words/Hofstadter/OriginalHFoundation.block`
- Truth anchor: `D5/S1/Words/Hofstadter/OriginalHFoundation.h_characterization`
- Truth anchor: `D5/S1/Words/Hofstadter/OriginalHFoundation.original_h_morphic_prefix`
- Truth anchor: `D5/S1/Words/Hofstadter/OriginalHFoundation.positive`
- Truth anchor: `D5/S1/Words/Hofstadter/OriginalHFoundation.tau`
- Truth anchor: `D5/S1/Words/Hofstadter/OriginalHFoundation.word`
- Truth anchor: `D5/S1/Words/Hofstadter/OriginalHFoundation.wordPrefix`
- Truth anchor: `D5/S1/Words/Hofstadter/OriginalHFoundation.word_characterization`
- Dependency: [D5/S1/Words/RankOneMorphismIterationBoundDefs](../RankOneMorphismIterationBoundDefs.md)
