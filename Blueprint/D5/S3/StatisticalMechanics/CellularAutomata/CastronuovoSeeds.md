# Complete cyclic and line seeds for a four-input cellular rule

## Abstract

One four-input rule admits a complete simple cyclic seed and a complete unrestricted line seed at k = 2. Every simple line seed omits XOR for this rule.

A letter is a Boolean function of k inputs. The initial alphabet consists of the two constant functions and the k projections. A simple seed uses each projection exactly once. A line seed has finitely many exceptions to a constant background, either 0 or 1, with 0 the paper's default. A cyclic seed of length N uses sites in Z/NZ and requires N at least the rule arity n. Completeness asks for every Boolean function to occur as a whole letter at some site and natural time, including time zero. The paper starts projection indices at one and this module starts at zero.

The rule updates site i from i−1, i, i+1, i+2, in that order, by φ(a,b,c,d) = ¬a ∧ ((b ∧ ¬c) ∨ d). The lifted update applies this formula pointwise for each assignment of the input variables.

The ring starts at sites 0 through 4 with (X,Y,0,0,1). A mask stores the value at (X,Y) in bit 2X+Y. The six rows are (12,10,0,0,15), (0,2,5,12,11), (4,14,9,0,3), (8,2,1,4,15), (0,6,13,8,3), and (12,10,1,0,7). The proof checks all thirty entries at each of the four assignments. Each mask from 0 through 15 appears.

**Theorem 1.1 (XOR is absent from every simple line orbit).**

$$\forall P \in \mathbb{Z} \to \operatorname{Letter}\left(2\right), \operatorname{SeedAlphabet}\left(P\right) \land \operatorname{Simple}\left(P\right) \implies \forall i \in \mathbb{Z}, t \in \mathbb{N}, \operatorname{orbit}\left(\operatorname{lineStep}\left(\varphi\right), t, P, i\right) \neq xorLetter$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds.simple_line_omits_xor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Niccolò Castronuovo, Alberto Dennunzio, Luciano Margara (2026). *Computing Functions Through the Orbits of Dynamical Systems: The Case of Cellular Automata*. DOI: [10.48550/arXiv.2610.34096](https://doi.org/10.48550/arXiv.2610.34096). URL: <https://arxiv.org/abs/2610.34096v1>.

*Commentary.*

For fixed Y, toggling X changes only its unique initial site. The usual Boolean order at even sites and its reverse at odd sites order the pair in a direction independent of Y. The signed monotonicity of the four local inputs preserves this order. At any output site and time the resulting order in X has the same direction for both choices of Y. XOR reverses that direction as Y changes. The argument uses the alphabet and simplicity and applies to both constant backgrounds.

**Theorem 1.2 (A complete simple ring with no complete simple line seed).**

$$\exists n \in \mathbb{N}, \varphi \in \operatorname{LocalRule}\left(n\right), k \in \mathbb{N}, 0 < n \land 0 < k \land \operatorname{StronglyCyclicUniversal}\left(\varphi, k\right) \land \neg\operatorname{StronglyUniversal}\left(\varphi, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds.question_5_9` (`✓ std3`). ∎

*Resolves.* `Problems/castronuovo-dennunzio-margara-2026-question-5-9` (proved) by `D5/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds.question_5_9`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"castronuovo-dennunzio-margara-2026-question-5-9","declaration_gid":"D5/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds.question_5_9","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Niccolò Castronuovo, Alberto Dennunzio, Luciano Margara (2026). *Computing Functions Through the Orbits of Dynamical Systems: The Case of Cellular Automata*. DOI: [10.48550/arXiv.2610.34096](https://doi.org/10.48550/arXiv.2610.34096). URL: <https://arxiv.org/abs/2610.34096v1>.

*Commentary.*

Question 5.9 quantifies over one positive arity n, one Boolean local rule φ of that arity, and one positive input count k. StronglyCyclicUniversal requires a complete simple cyclic seed at some legal ring length. StronglyUniversal requires a complete simple finite-background line seed. Here n = 4 and k = 2. The five-ring has length at least four, uses both projections once, and contains all sixteen target letters by time five.

**Theorem 1.3 (A complete unrestricted line seed with no complete simple line seed).**

$$\exists n \in \mathbb{N}, \varphi \in \operatorname{LocalRule}\left(n\right), k \in \mathbb{N}, 0 < n \land 0 < k \land \operatorname{Universal}\left(\varphi, k\right) \land \neg\operatorname{StronglyUniversal}\left(\varphi, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds.question_5_6` (`✓ std3`). ∎

*Resolves.* `Problems/castronuovo-dennunzio-margara-2026-question-5-6` (proved) by `D5/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds.question_5_6`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"castronuovo-dennunzio-margara-2026-question-5-6","declaration_gid":"D5/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds.question_5_6","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Niccolò Castronuovo, Alberto Dennunzio, Luciano Margara (2026). *Computing Functions Through the Orbits of Dynamical Systems: The Case of Cellular Automata*. DOI: [10.48550/arXiv.2610.34096](https://doi.org/10.48550/arXiv.2610.34096). URL: <https://arxiv.org/abs/2610.34096v1>.

*Commentary.*

Question 5.6 uses the same existential quantifiers. Universal permits any seed in the finite-background line family, including repeated projections. The witness consists of four copies of (X,Y,0,0,1) on the inclusive interval [−5,14] starting at −5, with zero elsewhere. All cones [i−t,i+2t] for 0 ≤ i ≤ 4 and 0 ≤ t ≤ 5 lie inside that interval. Periodic extension commutes with the update, so the checked ring letters also occur on this line.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds.question_5_6`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds.question_5_9`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds.simple_line_omits_xor`
