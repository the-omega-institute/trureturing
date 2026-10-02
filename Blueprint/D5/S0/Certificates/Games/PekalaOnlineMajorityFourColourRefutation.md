# Online majority edge-colouring at five to seven vertices

## Abstract

Four colours cannot guarantee online majority edge-colouring for every order from five to seven.

Pekala's Problem 11 asks whether Algorithm can use at most four colours against every Presenter strategy for final simple graphs on n in {5,6,7} vertices with minimum degree exactly two. The formal claim is the joint affirmative assertion for those three orders.

**Theorem 1.1 (No joint four-colour online strategy).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/PekalaOnlineMajorityFourColourRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/pekala-online-majority-four-colours` (refuted) by `D5/S0/Certificates/Games/PekalaOnlineMajorityFourColourRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"pekala-online-majority-four-colours","declaration_gid":"D5/S0/Certificates/Games/PekalaOnlineMajorityFourColourRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paweł Pękała (2026). *On-line majority edge-colourings of graphs*. URL: <https://arxiv.org/abs/2609.37973>.

*Commentary.*

A Lean-checked adaptive Presenter certificate on five vertices covers every normalized four-colour response. Each leaf has final minimum degree exactly two and a strict majority violation. This refutes the joint affirmative claim.

For six or seven vertices, continue each bad five-vertex play by connecting every new vertex to two old vertices other than a vertex where majority already fails. Each new vertex then has degree two, and the old violation survives all new colour choices. This extension answers each listed order negatively; it is a separate combinatorial argument.

## References

- Truth anchor: `D5/S0/Certificates/Games/PekalaOnlineMajorityFourColourRefutation.result`
