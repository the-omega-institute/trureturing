# Exact Dual Orthogonality for the Fixed-Sum Cubic

## Abstract

The actual unit cubic separates four-coordinate pivot spectra and gives an exact complete dual-frequency energy identity.

**Theorem 1.1 (The cubic removes the scaling ambiguity).**

$$\operatorname{CommRing}\left(R\right), \operatorname{IsUnit}\left(g\right) \implies \operatorname{InjOn}\left(spectralReading, AdmissiblePoint\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiDualPivotOrthogonality.spectral_reading_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any commutative ring R and parameters r,s,rho,sigma,g,h in R, with g a unit. For reduced pivot u=(alpha,beta), define a=r alpha+sigma beta and b=s alpha-rho beta. An admissible point z=(x,y) has a,b,x,y,h-x-y,x+y,h-x,h-y all units and satisfies g a b x y (h-x-y)=h. The spectral reading is (alpha x,alpha y,beta x,beta y). The theorem says that equality of these four readings for two admissible pivot-point pairs identifies both their reduced pivots and their points. It applies to composite rings, including ZMod(p^2), and uses no passage to a residue field.

Extract a unit t=x/x' from equality of the first-coordinate readings. It gives u'=t u. The reconstructed physical a is a unit, so the other two readings give y=t y'. The two original cubic equations then imply P_h(z)=t^2 P_h(z'). Expanding this equality gives t^2 x' y' (x'+y') (t-1)=0. The first factor is a unit, hence t=1. This is the essential separation argument; separation is not assumed as an input. For the original integer resonance coordinates, r rho+s sigma=p and p alpha=rho a+sigma b, p beta=s a-r b recover exactly the physical pivot formulas above.

**Theorem 1.2 (The full four-frequency average is exactly diagonal).**

$$q\neq 0 \land \operatorname{IsUnit}\left(g\right) \land \operatorname{AdmissibleFibres}\left(S, Z\right) \implies \frac{\sum_{f\in\operatorname{DualFrequency}\left(q\right)} \Vert \sum_{u\in S} \operatorname{c}\left(u\right) \operatorname{K}\left(u, f\right) \Vert^2}{q^4}=\sum_{u\in S} \Vert \operatorname{c}\left(u\right) \operatorname{chi}\left(u\right) \Vert^2 \operatorname{card}\left(\operatorname{Z}\left(u\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiDualPivotOrthogonality.complete_dual_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be any nonzero natural modulus, fix g a unit, and retain any finite reduced-pivot set S. Write AdmissibleFibres(S,Z) for the requirement that every point of every Z(u), for u in S, satisfies the admissible cubic and all the unit conditions above. Each Z(u) is finite, and further point deletions are permitted. For arbitrary complex pivot coefficients c and masks chi, define K(u;w,n)=chi(u) sum_{z in Z(u)} e_q((alpha w+beta n) dot z). The sum over all w,n in (ZMod q)^2 of |sum_{u in S} c(u) K(u;w,n)|^2, divided by q^4, equals sum_{u in S} |c(u) chi(u)|^2 card(Z(u)). There is no bound or nonvanishing assumption on c or chi. In particular q may be p^2.

The proof reuses Mathlib's orthogonality of finite additive characters. The four-coordinate reading embeds the actual pivot-point atoms into distinct characters, by the preceding unit-ring theorem. Expand the weighted square, sum the complete character Gram matrix, and retain exactly its diagonal. Reindexing the finite atoms by their pivot fibres gives the displayed cardinality factor. The normalization is the exact size q^4 of the full frequency group, rather than the size of a restricted frequency window.

This is a project derivation for the Pascadi dual-direction kernel, with no literature novelty claim. The spectrum is unprojected and the averaging period is complete. Positivity permits restricting the unnormalized energy to a frequency subset, but the identity supplies no normalized concentration bound in a short literal frequency box. That local concentration problem and the unrestricted original count remain separate.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiDualPivotOrthogonality.complete_dual_energy`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiDualPivotOrthogonality.spectral_reading_injective`
