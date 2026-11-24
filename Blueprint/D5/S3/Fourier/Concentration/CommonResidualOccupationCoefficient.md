# Cyclic occupation coefficients by common degree

## Abstract

A third polynomial degree records common occupation while character averaging selects the gap.

**Theorem 1.1 (A mixed coefficient for the common degree and frequency band).**

$$qM_{h,R} = (p!)^{2} \sum_{k \in \operatorname{ZMod}\left(q\right)}Q_{k}[p,p,h] \sum_{r \in R}X_{k}(r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CommonResidualOccupationCoefficient.common_residual_band` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a positive modulus q, a finite index set J, residues a(j), real weights w(j), total degree p, common degree h and a residue set R. The mass M with subscripts h and R counts ordered degree-p pairs having common degree h and signed gap in R, with multinomial weights.

In the local factor for j, two occupation counts u,v run from zero to p. Their term has degrees u,v,min(u,v), factorial coefficient w(j)^(u+v)/(u!v!) and the negative character at (u−v)a(j). Let Q with subscript k be the product of these local factors, and write X with subscript k for the positive character, for every k modulo q.

Coefficient selection in degrees (p,p,h) retains both totals and their common part. At the intermediate residue coefficient, a finite reindexing identifies the local coordinate choices with the pairs of occupation vectors. Fourier inversion applies the band filter. The case h=0 selects disjoint supports. At h=p the two vectors are equal and only the zero residue contributes.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/CommonResidualOccupationCoefficient.common_residual_band`
- Dependency: [D5/S3/Fourier/Concentration/CyclicDisjointOccupationCoefficient](CyclicDisjointOccupationCoefficient.md)
