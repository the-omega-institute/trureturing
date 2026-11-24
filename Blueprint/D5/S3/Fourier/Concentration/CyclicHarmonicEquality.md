# Equality for the First Two Cyclic Fourier Modes

## Abstract

When the second Fourier mode vanishes, saturation of the first requires a quarter turn.

Let q be a positive integer and let w be a nonnegative real weight of total mass one on ZMod q. Use the unnormalized discrete Fourier transform and write c for the squared magnitude at frequency one and s for the coefficient at frequency two. Write ord for additive order.

**Theorem 1.1 (The upper bound and all its equality cases).**

$$(s = 0 \implies c \leq \frac{1}{2}) \land (s = 0 \land c = \frac{1}{2} \iff \exists a, b \in \operatorname{ZMod}\left(q\right), a \neq b \land \operatorname{ord}\left(b-a\right) = 4 \land \operatorname{w}\left(a\right) = \frac{1}{2} \land \operatorname{w}\left(b\right) = \frac{1}{2} \land (\forall j \in \operatorname{ZMod}\left(q\right), j \neq a \land j \neq b \implies \operatorname{w}\left(j\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CyclicHarmonicEquality.zmod_first_mode_le_half_of_second_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume s=0 for the forward bound and classification. Let m be the first coefficient and z(j) the standard additive character evaluated at −j. The w-weighted variance of the real part of the conjugate of m times z(j) is c/2 minus c squared. At equality each positive mass has projected real part 1/2. Its projected imaginary part is then either 1/2 or −1/2. The imaginary mean vanishes, so both points occur with equal weights. Injectivity of the cyclic character gives exactly two residues, and the two phases differ by a quarter turn. Conversely, their squared phases cancel at frequency two, and the first coefficient is the average of two perpendicular unit phases.

On ZMod 4 a point mass has first squared magnitude one and second coefficient one. The nonnegative weight (1,1,0,0) has second coefficient zero and first squared magnitude two, with total mass two. The signed weight (1,1/2,−1/2,0) has total mass one and second coefficient zero, with first squared magnitude 5/2. Positive q supplies the finite DFT domain.

For the same positive modulus q, write E(q) for existence of a nonnegative weight of total mass one with second coefficient zero and squared first magnitude one half.

**Theorem 1.2 (Exactly the moduli that admit equality).**

$$\operatorname{E}\left(q\right) \iff 4 \mid q$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CyclicHarmonicEquality.zmod_exists_first_mode_half_of_second_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The additive order of the difference divides q. When four divides q, choose the residues zero and q/4. The two second-mode phases cancel, and the classification gives equality.

For a finite indexed lattice spectrum a(j) with nonnegative weights w(j) of total mass one, fix a frequency k modulo q. Send index j to the residue b(j)=a(j)k and sum its weight into the mass v at that residue. The same pushed-forward probability weight v supplies both modes. Expanding the sums by fibers recovers mode k of the original spectrum at mode one of v, and mode 2k at mode two of v. The classification then bounds the squared magnitude at k when the coefficient at 2k is zero. A quantitative bound for the high-order weighted collisions of actual zeta ordinates at positive resolution remains open.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/CyclicHarmonicEquality.zmod_exists_first_mode_half_of_second_zero`
- Truth anchor: `D5/S3/Fourier/Concentration/CyclicHarmonicEquality.zmod_first_mode_le_half_of_second_zero`
