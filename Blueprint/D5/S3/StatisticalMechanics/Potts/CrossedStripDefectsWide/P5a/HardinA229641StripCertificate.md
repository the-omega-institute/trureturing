# Finite vector relation for two-defect HDA strips

## Abstract

Finite vector relation for two-defect HDA strips

Continuation counts are resolved by the number of remaining monochromatic bonds. Zero-defect continuations follow the five-row proper-colouring transfer.

**Definition 1.1 (twoDefect).**

$$\forall (p: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), (\forall (q: \operatorname{HardinA233178Chromatic}.\operatorname{Column}), ((\operatorname{HardinA229641StripCertificate}.\operatorname{twoDefect}\left(p, q\right): \operatorname{Int}) = (\operatorname{if} (\operatorname{HardinA229538StripData}.\operatorname{cost}\left(p, q\right) = 2) \operatorname{then} 1 \operatorname{else} 0)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641StripCertificate.twoDefect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229641: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229641>.

*Commentary.*

This entry is one exactly when a cut contains two monochromatic bonds.

**Definition 1.2 (transfer).**

$$(\operatorname{HardinA229641StripCertificate}.\operatorname{transfer}: \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right)\right), \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right)\right), \operatorname{Int}\right)) = \operatorname{Matrix}.\operatorname{fromBlocks}\left(\operatorname{HardinA233178Chromatic}.\operatorname{T}, \operatorname{Matrix}.\operatorname{fromCols}\left(\operatorname{HardinA229538StripData}.\operatorname{oneDefect}, \operatorname{HardinA229641StripCertificate}.\operatorname{twoDefect}\right), (0: \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right), \operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{Int}\right)), \operatorname{HardinA229538StripData}.\operatorname{transfer}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641StripCertificate.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229641: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229641>.

*Commentary.*

The left summand has budget two. The inherited right summand has budgets one and zero.

**Definition 1.3 (terminal).**

$$(\operatorname{HardinA229641StripCertificate}.\operatorname{terminal}: \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{Sum}\left(\operatorname{HardinA233178Chromatic}.\operatorname{Column}, \operatorname{HardinA233178Chromatic}.\operatorname{Column}\right)\right) \to \operatorname{Int}) = \operatorname{Sum}.\operatorname{elim}\left((0: \operatorname{HardinA233178Chromatic}.\operatorname{Column} \to \operatorname{Int}), \operatorname{HardinA229538StripData}.\operatorname{terminal}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641StripCertificate.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229641: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229641>.

*Commentary.*

An empty continuation requires a remaining budget of zero.

**Definition 1.4 (coefficients641).**

$$(\operatorname{HardinA229641StripCertificate}.\operatorname{coefficients641}: \operatorname{Fin}\left(30\right) \to \operatorname{Int}) = \operatorname{Matrix}.\operatorname{vecCons}\left((-46656), \operatorname{Matrix}.\operatorname{vecCons}\left(279936, \operatorname{Matrix}.\operatorname{vecCons}\left(186624, \operatorname{Matrix}.\operatorname{vecCons}\left((-4611168), \operatorname{Matrix}.\operatorname{vecCons}\left(7359984, \operatorname{Matrix}.\operatorname{vecCons}\left(21460464, \operatorname{Matrix}.\operatorname{vecCons}\left((-73617984), \operatorname{Matrix}.\operatorname{vecCons}\left(9610272, \operatorname{Matrix}.\operatorname{vecCons}\left(227616084, \operatorname{Matrix}.\operatorname{vecCons}\left((-273411640), \operatorname{Matrix}.\operatorname{vecCons}\left((-168525432), \operatorname{Matrix}.\operatorname{vecCons}\left(522690894, \operatorname{Matrix}.\operatorname{vecCons}\left((-138135927), \operatorname{Matrix}.\operatorname{vecCons}\left((-412178619), \operatorname{Matrix}.\operatorname{vecCons}\left(287096430, \operatorname{Matrix}.\operatorname{vecCons}\left(147888798, \operatorname{Matrix}.\operatorname{vecCons}\left((-190067859), \operatorname{Matrix}.\operatorname{vecCons}\left((-12632640), \operatorname{Matrix}.\operatorname{vecCons}\left(66347438, \operatorname{Matrix}.\operatorname{vecCons}\left((-7797810), \operatorname{Matrix}.\operatorname{vecCons}\left((-13478352), \operatorname{Matrix}.\operatorname{vecCons}\left(2851598, \operatorname{Matrix}.\operatorname{vecCons}\left(1614489, \operatorname{Matrix}.\operatorname{vecCons}\left((-424479), \operatorname{Matrix}.\operatorname{vecCons}\left((-108707), \operatorname{Matrix}.\operatorname{vecCons}\left(31983, \operatorname{Matrix}.\operatorname{vecCons}\left(3468, \operatorname{Matrix}.\operatorname{vecCons}\left((-1191), \operatorname{Matrix}.\operatorname{vecCons}\left((-15), \operatorname{Matrix}.\operatorname{vecCons}\left(18, \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641StripCertificate.coefficients641` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229641: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229641>.

*Commentary.*

The entries are ordered from the smallest shift of the recurrence to the largest.

**Theorem 1.5 (vector_polynomial).**

$$\operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA229641StripCertificate}.\operatorname{transfer})^{33}, \operatorname{HardinA229641StripCertificate}.\operatorname{terminal}\right) = \sum_{(k: \operatorname{Fin}\left(30\right))} (\operatorname{SMul}.\operatorname{smul}\left(\operatorname{HardinA229641StripCertificate}.\operatorname{coefficients641}\left(k\right), \operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{HardinA229641StripCertificate}.\operatorname{transfer})^{(3) + (\operatorname{Fin}.\operatorname{val}\left(k\right))}, \operatorname{HardinA229641StripCertificate}.\operatorname{terminal}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641StripCertificate.vector_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229641: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229641>.

*Commentary.*

The relation holds simultaneously for all boundary columns and all three residual budgets.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641StripCertificate.coefficients641`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641StripCertificate.terminal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641StripCertificate.transfer`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641StripCertificate.twoDefect`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641StripCertificate.vector_polynomial`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic](../../../../Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate](HardinA229538StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData](HardinA229538StripData.md)
