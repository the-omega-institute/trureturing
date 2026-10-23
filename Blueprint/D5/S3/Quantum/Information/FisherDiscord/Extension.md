# Flagged Fisher-discord extensions

## Abstract

Flagged extensions of diagonal density matrices have zero Fisher discord.

**Definition 1.1 (Classical flag extension).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Extension.flagExtension`

*Formalization.* `D5/S3/Quantum/Information/FisherDiscord/Extension.flagExtension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite diagonal weight function w, the flagged matrix places w(i) on the product basis vector (i,i) and zero elsewhere. The second factor records the first-factor index.

**Theorem 1.2 (Flag marginal).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Extension.flag_partialTrace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FisherDiscord/Extension.flag_partialTrace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the second-factor partial trace of the flagged matrix returns the diagonal matrix with entries w(i).

**Theorem 1.3 (Zero discord of a flag).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Extension.flag_discord_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FisherDiscord/Extension.flag_discord_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative weights, every Hermitian SLD solution on the flagged matrix gives zero Fisher discord for an observable lifted from the first factor.

**Definition 1.4 (Extension inequality).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Extension.extensionIneq`

*Formalization.* `D5/S3/Quantum/Information/FisherDiscord/Extension.extensionIneq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The extension inequality compares the discord of a fixed diagonal marginal and observable with every state having that marginal and every admissible Hermitian SLD.

**Theorem 1.5 (Classification of diagonal marginals).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Extension.monotone_iff_discord_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FisherDiscord/Extension.monotone_iff_discord_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For normalized nonnegative diagonal weights and a Hermitian observable, the extension inequality holds in every finite second dimension exactly when the marginal Fisher discord is zero.

## References

- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Extension.extensionIneq`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Extension.flagExtension`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Extension.flag_discord_zero`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Extension.flag_partialTrace`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Extension.monotone_iff_discord_zero`
- Dependency: [D5/S3/Quantum/Information/FisherDiscord/Spectral](Spectral.md)
