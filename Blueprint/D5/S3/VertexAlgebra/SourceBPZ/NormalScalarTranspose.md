# Original integer scalar insertion transpose

## Abstract

NormalScalarTranspose

The carrier is the original finite-charge direct sum of complex oscillator polynomials. B is complex bilinear, with its input order retained. No half-current or tensor carrier, symmetry, nondegeneracy, positivity, rank restriction, or all-source invariance is assumed. The normal product and divided derivative retain the Carnahan/native adaptation attribution of FieldNormalProduct. This is a classical finite normal-order calculation; no literature novelty is claimed.

**Definition 1.1 (insertion).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/NormalScalarTranspose.insertion`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/NormalScalarTranspose.insertion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every lattice D, coordinate i, natural derivative order p and actual vertex operator F, insertion is the actual normalMinusOne of dividedDerivative p (neutralField D i) with F. Thus its source oscillator is h_i(-(p+1)); it is not a newly reflected field.

**Theorem 1.2 (consumed_normal_product_form).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/NormalScalarTranspose.consumed_normal_product_form`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/NormalScalarTranspose.consumed_normal_product_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix arbitrary D, a complex bilinear B on Carrier D, a coordinate i, derivative order p, actual tail field F, an arbitrary label type with finite subset S, actual fields G(a), complex coefficients lambda(a), integer reflection constants K(a), and complex charge kappa. Assume B(h_i(k)x,y)=-B(x,h_i(-k)y) for every integer k and both inputs; B(F[t]x,y)=sum over a in S of lambda(a) B(x,G(a)[K(a)-t]y) for all t,x,y; and h_i(0)G(a)[t]x=G(a)[t]h_i(0)x+kappa G(a)[t]x for a in S. The tail premise concerns F only and assumes no normal-product transpose.

For every integer m and inputs u,v, B(insertion(p,F)[m]u,v) equals (-1)^(p+1) times the sum over a in S of lambda(a) multiplied by: the sum over s=0,...,p of choose(p+1,s+1) B(u,insertion(s,G(a))[K(a)+p+s+2-m]v), plus kappa B(u,G(a)[K(a)+p+1-m]v). Equivalently n=p+1 and r=s+1 range through n>=1 and 1<=r<=n. The final term deletes the oscillator and never invokes a derivative of order -1.

The actual constructor's two vector sums have finite support before scalar evaluation. With A=vectorFrequencyBound(u)+1 and C=vectorFrequencyBound(v)+1 the scalar intervals are k=1-C,...,-1 and k=0,...,A-1. The omitted derivative band -p<=k<0 has zero integer choose(-k-1,p). Finite reflection j=-k and integer Vandermonde give -choose(j-1,p)=(-1)^(p+1) sum over s=0,...,p of choose(p+1,s+1)choose(-j-1,s). Only the j=0 ordering boundary uses the charge covariance and produces the displayed kappa term.

The consumer is the cons step of the original wordField BPZ induction: F is the tail wordField, G(a) are the finite lowered or deleted tail words, K(a) their exact opposite-mode constants, and kappa is bilinear(unitCharge i,alpha). At p=0 a singleton primary tail gives the nonprimary correction B(u,G[K+1-m]v) with coefficient -lambda*kappa. This unit does not construct the original pairing or charged-primary law, prove the word induction or permutation bridge, assemble the finite L1 source flow, or establish full VOA, CFT, fusion, string theory or AdS/CFT.

## References

- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/NormalScalarTranspose.consumed_normal_product_form`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/NormalScalarTranspose.insertion`
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraCurrents](../LatticeSugawaraCurrents.md)
