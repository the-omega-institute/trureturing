# Original circle modes between Sobolev spaces

## Abstract

Bounded Sobolev extensions of the literal original charged circle modes.

For the original positive Model, write d=chargeEnergy(D,a) and q=order(a)=2*d.toNat. Positivity gives d>=0. The circle mode mode(a,m) is literally actualField(D,a)[[m+d-1]] on Carrier(D), for every integer m. At a=0 the identity-field formula leaves only m=0. If the lattice has rank zero, every charge is zero, so this same branch covers that case.

The existing original charged energy bound supplies a positive modeConstant(a)=C_a, chosen before every mode m and finite input v. The zero-charge branch uses C=1. On an input grade E, the actual mode lands in E-m. Negative output grades vanish by OriginalWordEnergy. On a surviving output grade, E-m+1<=(1+abs(m))*(E+1) controls its Sobolev weight. The proof then uses energy_bound_of_grades from OriginalNeutralEnergy to recombine distinct orthogonal shifted output grades. Thus the estimate applies to arbitrary finite mixed inputs without a support multiplier; it does not promote a scalar inequality to an unproved operator inequality.

For every k>=0, the resulting estimate is normD(T^k mode(a,m)v)<=C_a*(1+abs(m))^(q+k)*normD(T^(q+k)v), where T is the actual 1+Sugawara zero mode. Mathlib's extendOfNorm along the dense original embedding constructs modeExtension(a,k,m):H_(q+k)->H_k. Its operator norm is at most C_a*(1+abs(m))^(q+k), and it sends each embedded finite vector to the embedded literal mode image.

Equality on the dense original carrier proves compatibility of the extensions under every Sobolev inclusion H_k->H_j with j<=k. OriginalInfiniteSmearing consumes these bounds and compatibility to sum all integer modes in the actual Banach operator space. OriginalSmoothDomain uses the finite-state agreement to extend the original opposite-charge pairing. These are consumed support components, with no separate theorem Describe or all-state field claim. The smooth-smearing motivation is Carpi and Tomassini, arXiv:2303.14097v2; the original charged-field and Mathlib suppliers retain their existing attributions.

## References

- Dependency: [D5/S3/VertexAlgebra/Analysis/OriginalSobolev](OriginalSobolev.md)
