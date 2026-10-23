# Parameter jets and public coefficient arrays

## Abstract

Parameter differentiation commutes with finite Lorentz histories, with common-scale bounds and public-array regularity.

All parameter derivatives act on the actual finite common-grid history. Finite samples give a continuous linear coefficient functional, so differentiation commutes with the entire history. The reference profile is 1/2+eta*phi((a+d*q)/x), with phi(t)=chi(t)*t^beta for a smooth compactly supported chi whose support lies in the positive half-line.

For r<rho<r+1 there is B>=2. For each b>=B, xstar>0, N>=r+1 and parameter order m there is one C>0, independent of ring j, point x, stage k and coefficient index. Whenever 0<x<=1 and s(j)/sqrt(b)<=x, every mth parameter derivative of a center coefficient is bounded by C*s(j)^(-m). Every derivative of an increment coefficient at the next degree is bounded by C*s(j)^(-m-rho)*n(j,k+1)^(-rho/2). For every ell<=r and q in [0,1], the ell-th q residual for the mth parameter jet is bounded by C*s(j)^(-m-rho)*delta(n(j,k),q)^(rho-ell). The same b,N and finite history occur in all three clauses.

The public-array construction uses the smooth bump expNegInvGlue(9/16-z^2), its locally finite natural-translate denominator, the logarithmic coordinate 2*log(xstar/x)/log(b), and the resulting normalized ring weights. Startup rings beyond the current stage contribute the common value 1/2. Multiplication by W*x^beta and centering at 1/2 gives the public lower and upper arrays.

Assume the compact cutoff lies in (0,T), T>0, 0<=chi<=1, beta>=0, r<rho<r+1, rho>=2 and theta>0. There is B>=16 such that each b>=B and 0<xstar<=1 admits D>0,N>=3*r+2, chosen before W. For every W>=0 with W*xstar^beta<=15/16, every stage and legal index, both arrays are smooth at every 0<x<=xstar, lie in order between 1/32 and 31/32, and differ from 1/2 by at most W*x^beta/2. They obey both elevation inequalities including startup terms. If beta>0, each fixed coefficient function is continuous on [0,xstar]. At each fixed positive x the width eventually has a C*(N*b^k)^(-rho/2) bound, uniformly over legal indices, and tends to zero.

These conclusions do not give a width estimate uniform in x, target sandwiching or target identification, uniform weight-derivative bounds, a full C^beta bound for the public coefficients, or higher-order gluing at zero. The cutoff is smooth; no triangular ring weight is treated as smooth.

**Theorem 1.1 (Linear iterated).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.linear_iterated`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.linear_iterated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

A continuous real linear map between arbitrary real normed spaces commutes with the mth derivative at x whenever the input function is C^m at x.

**Theorem 1.2 (Reference transport).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.reference_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.reference_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

For positive tau,b, smooth phi, x>0 and arbitrary natural r,k,D,J,m, the mth parameter derivative of the actual center's degree-D coefficient equals that coefficient of the actual center applied to the mth parameter derivative of the reference input. The coefficient indices need not satisfy J<=D.

**Theorem 1.3 (Reference center mixed scales).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.reference_center_mixed_scales`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.reference_center_mixed_scales` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

The three common-scale estimates above hold for the same reference input, parameter jet, b and N; no complete low-order function norm is introduced.

**Theorem 1.4 (Active ring).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.active_ring`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.active_ring` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

If xstar,x>0, b>1 and the jth normalized scale weight is nonzero, then s(j)/sqrt(b)<=x. This connects the actual bump support to the ring hypotheses.

**Theorem 1.5 (Coefficient smooth).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.coefficient_smooth`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.coefficient_smooth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

For positive tau,b and smooth phi, every coefficient of every finite actual reference-center history is smooth at each x>0, for all natural r,k,D,t.

**Theorem 1.6 (Reference public array regular).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.reference_public_array_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.reference_public_array_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Olga Holtz; Fedor Nazarov; Yuval Peres (2011). *New Coins from Old, Smoothly*. DOI: [10.1007/s00365-010-9108-5](https://doi.org/10.1007/s00365-010-9108-5). URL: <https://arxiv.org/abs/0808.1936v3>.

*Commentary.*

The four groups of conclusions in the introduction retain the shared D,N, the dependence of eventual constants on the fixed positive x, and the strict beta>0 premise for continuity at zero.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.active_ring`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.coefficient_smooth`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.linear_iterated`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.reference_center_mixed_scales`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.reference_public_array_regular`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport.reference_transport`
- Dependency: [D5/S3/Analytic/SeriesInequalities/HNPCorrectionLiftAdvantage](HNPCorrectionLiftAdvantage.md)
