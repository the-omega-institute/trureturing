# Balanced five-mode terminal word rank

## Abstract

Uniform homogeneous rank for the balanced five-mode reflection family under injective algebra transport.

**Theorem 1.1 (Exact rank with a faithful lift and nonzero weights).**

$$\forall E \in \operatorname{FiniteDimensionalComplexAlgebra}\left(\right), f \in \operatorname{AlgHom}\left(\mathbb{C}, \operatorname{Matrix}\left(5, 5, \mathbb{C}\right), E\right), a \in \mathbb{C}, b \in \mathbb{C}, c \in \mathbb{C}, z \in \mathbb{C}, w \in \mathbb{C}, n \in \mathbb{N},\; \left(\operatorname{Injective}\left(f\right) \land \left(a^{2} + b^{2} = 1 \land \left(2 \cdot c^{2} = 1 \land \left(b \ne 0 \land \left(c \ne 0 \land \left(a \ne 1 \land \left(z \ne 0 \land w \ne 0\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{finrank}\left(\mathbb{C}, \operatorname{wordSpace}\left(\operatorname{smul}\left(z, \operatorname{apply}\left(f, \operatorname{reflection0}\left(a, b\right)\right)\right), \operatorname{smul}\left(w, \operatorname{apply}\left(f, \operatorname{reflection1}\left(c\right)\right)\right), n\right)\right) = \operatorname{min}\left(n + 1, 4\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/BalancedFiveModeWordRank.framed_balanced_word_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

U=reflection0(a,b) and V=reflection1(c) are the explicit five-by-five matrices in the Lean source. U has the block [[a,b],[b,-a]] on configurations 0 and 4 and fixes configurations 1,2,3. V is the symmetric signed square, with coefficient c, negative edge 0–3, and fixed configuration 4. The parameters are complex; no positivity or self-adjointness is required by this algebraic theorem. E is any finite-dimensional complex algebra and f is an injective unital complex algebra homomorphism.

For R=UV the proof establishes R^4+(a+1)R^3-(a+1)R-I=0 and independence of I,R,R^2,R^3. Entries (0,0),(0,4),(4,0),(1,2) form a minor of determinant c b^2(1-a), nonzero under the stated assumptions. The quartic supplies both forward and inverse power-space closure. These facts provide the lower and upper bounds at every length through TwoInvolutionWordRank.homogeneous_word_rank.

For the fixed V2 source in RECURSIVE_RELATIONAL_OBSERVATION_MINIMAL_RECORD_DILATIONS, equations (1.2),(1.3),(2.6),(2.8), restrict p=q>0, r>0, 2p+r<1. Put A=1-2p-r, B=1-2p, t=2p, a=sqrt(A)/sqrt(B), b=sqrt(r)/sqrt(B), c=1/sqrt(2), z=sqrt(B), w=sqrt(t). The published frames G=(I,-iX,iY,-iZ,-iY) give f(X)=D†(X⊗I₂)D on all C⁵⊗C², where D is the block diagonal matrix of G_i†. The exact published operators are z f(U) and w f(V). All strict parameters obey the displayed hypotheses, without a probability cutoff.

Composition with independently supplied fresh environments gives the exact length-N Kraus products. Watrous, The Theory of Quantum Information, Chapter 2, Theorem 2.22 and Corollary 2.27, and Sanz, Pérez-García, Wolf and Cirac, A quantum version of Wielandt’s inequality, arXiv:0909.5347, Section II, supply the standard Choi vectorization and minimum pure-environment interpretation: the terminal rank is min(N+1,4). This yields an abstract terminal pure environment and equality on every untouched reference extension. The original one-step minimum, measured flag recovery and two-step unread comparison remain their existing owners.

Repeated action of the published balanced controlled interaction on the same retained environment has period two and is distinct from these channel powers. The terminal dimension does not supply measured Markov histories, independent arbitrary coherent path archives, native alpha/beta acquisition, physical controls, finite precision or actual record outputs. An unlimited archive bound requires a separate input and readout contract.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/BalancedFiveModeWordRank.framed_balanced_word_rank`
- Dependency: [D5/S3/Quantum/QuantumChannels/TwoInvolutionWordRank](TwoInvolutionWordRank.md)
