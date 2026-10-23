# Generator Row Order Necessity

## Abstract

Folded characters at variable even order obstruct a uniform generator-row coefficient.

**Theorem 1.1 (Complete inverse-signal family and quadratic coefficient floor).**

Lean statement: `D5/S3/Fourier/GeneratorRowOrderNecessity.parameter_family`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/GeneratorRowOrderNecessity.parameter_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural M>=32, set N=2M, q=ZMod.stdAddChar, F(k)=1 and J(k)=q(k) when k.val<=M, J(k)=q(-k) otherwise. Both signals are actual complex inverse transforms f=ZMod.dft.symm F and g=ZMod.dft.symm J. Mathlib's forward DFT is unnormalized with negative exponent. Both exact complex DC values equal 1, and every spectral norm equals 1. No real or positive time-domain assumption is imposed.

For B(H;k,l)=H(k)H(l)conj(H(k+l)), the entire zero row agrees. The target generator row equals 1 below k.val<M and q(2) at the midpoint and beyond, including the cyclic wrap entry k=N-1. The source row is identically 1. Every raw complex residual has norm at most epsilon=4*pi/N, with 0<epsilon<=1/4. The chord estimate uses the original integer-two exponential formula and Real.norm_exp_I_mul_ofReal_sub_one_le.

The actual counting squared error sum_x |g(x)-f(x-t)|^2 equals exactly 1 at t=1 and t=-1 and exactly 2 at every other translation. The proof uses the original cyclic_parseval and dft_translation, whose counting Parseval factor is 1/N. Folded evenness and J+conj(J)=q+conj(q) reduce twice the real correlation to primitive character sums. Orthogonality applies at composite orders and to nonunit frequencies; no prime-order or sampled translation restriction is present.

The existing GeneratorRowStability.sourceEnergy of f is (N-1)/N. For every real K, the original existential premise that some actual translation has counting squared error <= K*epsilon^2*sourceEnergy(f) implies K>=N^3/(16*pi^2*(N-1))>N^2/(16*pi^2). No K>=0 premise is added; zero and negative K remain quantified and fail the original bound premise. The family theorem states these observations, identities and implication as a direct conjunction.

**Theorem 1.2 (No single finite coefficient over all requested even orders).**

Lean statement: `D5/S3/Fourier/GeneratorRowOrderNecessity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/GeneratorRowOrderNecessity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal Prop claim asks for one real C>=0 for all M>=32, N=2M, all actual complex f,g and all 0<=epsilon<=1/4 with exact complex DC1, both unit spectra, exact zero row and every cyclic generator residual bounded by epsilon. It requires an actual translation whose counting squared error is <=C*epsilon^2*GeneratorRowStability.sourceEnergy(f). The designated theorem has the literal type Not claim.

Choose natural M>max(32,8*(C+1)) and apply the complete inverse-signal family at epsilon=4*pi/N. Its original coefficient implication forces C above a floor strictly exceeding N^2/(16*pi^2). The bound pi<4 and the chosen M make this exceed C, including C=0. This refutes a single finite coefficient under the full ambient observed-input contract. It makes no literature-novelty, sharp-constant or positive-real-signal claim. Order-dependent estimates and complete-bispectrum estimates retain their own hypotheses and conclusions.

## References

- Truth anchor: `D5/S3/Fourier/GeneratorRowOrderNecessity.parameter_family`
- Truth anchor: `D5/S3/Fourier/GeneratorRowOrderNecessity.result`
- Dependency: [D5/S3/Fourier/FinitePoisson](FinitePoisson.md)
- Dependency: [D5/S3/Fourier/FullBispectrumStability](FullBispectrumStability.md)
- Dependency: [D5/S3/Fourier/GeneratorRowStability](GeneratorRowStability.md)
