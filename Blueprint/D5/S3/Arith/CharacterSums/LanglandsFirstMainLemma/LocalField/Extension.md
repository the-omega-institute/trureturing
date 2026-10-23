# Extension norm and conjugates

## Abstract

Norms and conjugates in the extension module retained by the supplier imports.

**Theorem 1.1 (The norm is the product of Galois conjugates).**

Lean statement: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/Extension.galoisConjugates_prod`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/Extension.galoisConjugates_prod` (`✓ std3`). ∎

*Citation.* fukubillueda-web contributors (2026). *epsilon_FML finite-field Hasse–Davenport supplier*. URL: <https://github.com/fukubillueda-web/epsilon_FML/tree/b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed>.

*Commentary.*

For fields F and K with Algebra F K, FiniteDimensional F K and IsGalois F K, galoisConjugates F K x is the multiset of σ(x) indexed by Gal(K/F). For every x in K its product equals algebraMap F K (norm F K x), where norm is Algebra.norm. Conjugates are counted by automorphisms with multiplicity. The parallel sum identity gives Algebra.trace, and the multiset cardinality is Module.finrank F K.

HasseDavenportLift directly imports Extension, which imports ResidueField. This is a retained import dependency: the selected lifting proof uses Mathlib's Algebra.norm and Algebra.trace through CharacterAPI and minimal-polynomial identities, without invoking galoisConjugates_prod. The local-field ramification and norm-order results elsewhere in Extension impose no extra hypotheses on the lift.

Source: epsilon_FML at immutable commit b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed, LanglandsFirstMainLemma/LocalField/Extension.lean; Apache-2.0. The exact license and original source hashes are in Library/Fourier/epsilonfml2026hassedavenport.md. This is attributed upstream support, not a new theorem or open-problem resolution.

Supplier escape registration remains unfinished under https://github.com/the-omega-institute/trureturing/issues/5214: the original finite-field character/norm/trace telescope has no supplied faithful enrolled template with compiled audit evidence. This narrative does not complete that audit.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/Extension.galoisConjugates_prod`
- Dependency: [D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/ResidueField](ResidueField.md)
