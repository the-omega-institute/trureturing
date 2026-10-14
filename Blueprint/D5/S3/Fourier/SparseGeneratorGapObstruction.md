# Sparse Generator Gap Obstruction

## Abstract

Sparse symmetric cyclic generators with a uniform ordinary gap force a logarithm-squared coefficient loss.

**Theorem 1.1 (Actual generating sets and calibrated inverse signals).**

Lean statement: `D5/S3/Fourier/SparseGeneratorGapObstruction.parameter_family`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/SparseGeneratorGapObstruction.parameter_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer N>=ceil(exp(128)), let L=log(N), q=ceil(16L) and r=floor(L/16). A fixed choice by N gives an actual nonzero symmetric generating Finset S of cardinality 2q. Its ordinary gap is the minimum, over every nonzero cyclic frequency a, of the average squared standard-character chord |chi(a*s)-1|^2, and is at least 1. The empty frequency domain is explicitly assigned gap zero. No multiset, prime-order restriction or subsequence replaces this family.

Independent uniform samples exclude two-torsion and signed collisions while bounding all nontrivial character averages. Primitive character orthogonality applies to composite orders and nonunit frequencies. Positive gap forces generation through the existing finite annihilator cardinality theorem. The symmetric Cayley graph is connected, and delta(k) is its distance to the anchor set {0} union S.

The phase u(k)=exp(I*pi/2*min(delta(k)/r,1)) has unit norm, u(0)=1 and u(s)=1 for every generator. The actual signals are f=dft.symm(1) and g=dft.symm(u), under the unnormalized negative-exponent forward DFT. Both complex DC values equal 1; the entire zero bispectrum row agrees. Every complete raw generator row, including cyclic wraps, has residual norm at most epsilon=pi/(2r), where 0<epsilon<=pi/16<1/4.

Commutativity sends shortest walks, with zero padding, to the existing symmetric power Sym(Option S,r). Its cardinality is choose(|S|+r,r). The weighted term in (1+1/512)^(|S|+r) bounds the phase-support cardinality by sqrt(N). Outside this support u=I, and everywhere |u-I|<=sqrt(2). Character cancellation and the original cyclic Parseval and translation identities give, for every actual translation t, counting squared error in [2-2sqrt(2)/sqrt(N),2+2sqrt(2)/sqrt(N)].

The existing sourceEnergy(f) is exactly (N-1)/N. For every real K, if some actual translation satisfies error<=K*epsilon^2*sourceEnergy(f)/ordinaryGap(S), then K>=L^2/(256*pi^2). This retains the existential actual-signal antecedent, including zero and negative K, and states the complete family as a direct conjunction.

**Theorem 1.2 (No finite uniform coefficient for the full observed-input claim).**

Lean statement: `D5/S3/Fourier/SparseGeneratorGapObstruction.result`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/SparseGeneratorGapObstruction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal Prop claim quantifies one real C>=0 over every positive cyclic order, every actual nonempty nonzero generating Finset S with positive ordinary gap, arbitrary complex signals f,g, and arbitrary m>0 and 0<=epsilon<=m^3/4. It assumes exact complex DC equality, the source spectral floor m, and bounds on the complete raw zero and S rows. It asks for an actual translation with counting squared error at most C*epsilon^2*sourceEnergy(f)/(m^6*ordinaryGap(S)). Symmetry, generator calibration, unit spectra, logarithmic cardinality and large order are properties of the counterfamily, not additional ambient premises.

The literal theorem Not claim chooses N=ceil(exp(128+16*pi*(C+1))) and applies the complete family at m=1. Its unchanged coefficient implication contradicts the choice of N, including C=0. The statement imposes no real or positive time-domain signal assumption, and makes no claim of a sharp constant or literature novelty.

## References

- Truth anchor: `D5/S3/Fourier/SparseGeneratorGapObstruction.parameter_family`
- Truth anchor: `D5/S3/Fourier/SparseGeneratorGapObstruction.result`
- Dependency: [D5/S3/Fourier/SparseGeneratorFamily](SparseGeneratorFamily.md)
