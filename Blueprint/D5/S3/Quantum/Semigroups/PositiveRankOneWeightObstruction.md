# Positive rank-one obstruction to weighted L∞ contraction

## Abstract

A positive rank-one semigroup on the unit interval has no equivalent contractive weighted essential sup norm.

Madou–Remizov–Vafadar (eds.), Open problems in one-parameter operator semigroups theory, arXiv:2410.00416v2, §6, Problem 22, equation (3), asks for g>0 almost everywhere with g and 1/g essentially bounded and ‖gT(t)f‖∞≤‖gf‖∞ for every complex f in L²∩L∞. The comments on p. 18 suggest positivity as a restriction. This result gives a positive counterexample in the bounded, self-adjoint, full-domain angle-zero case. It does not settle Problems 21, 23 or 24, and does not claim a first resolution of the unrestricted Problem 22 or literature priority.

**Definition 1.1 (The unit-interval measure).**

$$mu = \operatorname{restrict}\left(volume, \operatorname{Ioo}\left(0, 1\right)\right)$$

*Formalization.* `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.μ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. Madou; I. Remizov; M. Vafadar (eds.) (2024). *Open problems in one-parameter operator semigroups theory*. DOI: [10.48550/arXiv.2410.00416](https://doi.org/10.48550/arXiv.2410.00416). URL: <https://arxiv.org/abs/2410.00416v2>.

*Commentary.*

The measure is real Lebesgue measure restricted to (0,1). Its total mass is one; in particular it is finite and sigma-finite.

**Definition 1.2 (The actual complex L2 space).**

$$H = \operatorname{Lp}\left(\mathbb{C}, 2, mu\right)$$

*Formalization.* `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.H` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. Madou; I. Remizov; M. Vafadar (eds.) (2024). *Open problems in one-parameter operator semigroups theory*. DOI: [10.48550/arXiv.2410.00416](https://doi.org/10.48550/arXiv.2410.00416). URL: <https://arxiv.org/abs/2410.00416v2>.

*Commentary.*

H is Mathlib's complex Lp at exponent 2 over mu. Every essential sup norm in the claim uses this same measure.

**Definition 1.3 (The L2 vector with vanishing essential floor).**

$$h = \operatorname{toLp}\left((x: \mathbb{R})\mapsto \operatorname{ofReal}\left(x\right)\right)$$

*Formalization.* `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.h` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. Madou; I. Remizov; M. Vafadar (eds.) (2024). *Open problems in one-parameter operator semigroups theory*. DOI: [10.48550/arXiv.2410.00416](https://doi.org/10.48550/arXiv.2410.00416). URL: <https://arxiv.org/abs/2410.00416v2>.

*Commentary.*

The toLp class is constructed from the proved square-integrability of x↦(x:ℂ). Its representative equals x almost everywhere, and its squared Hilbert norm is exactly 1/3.

**Definition 1.4 (The orthogonal rank-one projection).**

$$P = \operatorname{starProjection}\left(\operatorname{spanC}\left(h\right)\right)$$

*Formalization.* `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.P` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. Madou; I. Remizov; M. Vafadar (eds.) (2024). *Open problems in one-parameter operator semigroups theory*. DOI: [10.48550/arXiv.2410.00416](https://doi.org/10.48550/arXiv.2410.00416). URL: <https://arxiv.org/abs/2410.00416v2>.

*Commentary.*

The existing orthogonal projection onto the complex span of h is used directly. The compiled representative formula is P f(x)=3 x ∫ y f(y) dmu(y), for every complex L2 input f. The inner product in Lean is conjugate-linear in its first argument; therefore P f=3⟨h,f⟩h. This operator is idempotent and positive on real nonnegative representatives.

**Definition 1.5 (The bounded nonnegative generator).**

$$A = I - P$$

*Formalization.* `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.A` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. Madou; I. Remizov; M. Vafadar (eds.) (2024). *Open problems in one-parameter operator semigroups theory*. DOI: [10.48550/arXiv.2410.00416](https://doi.org/10.48550/arXiv.2410.00416). URL: <https://arxiv.org/abs/2410.00416v2>.

*Commentary.*

A is I−P, equivalently the orthogonal projection onto the orthogonal complement of h. It is bounded and self-adjoint, and ⟨u,Au⟩=‖Au‖². The zero eigenvector h is retained; no strict coercivity or strict spectral stability is assumed.

**Definition 1.6 (The actual complex-time semigroup).**

$$\forall z: \mathbb{C}, \operatorname{T}\left(z\right) = P + \operatorname{smul}\left(\operatorname{exp}\left(-(z)\right), A\right)$$

*Formalization.* `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. Madou; I. Remizov; M. Vafadar (eds.) (2024). *Open problems in one-parameter operator semigroups theory*. DOI: [10.48550/arXiv.2410.00416](https://doi.org/10.48550/arXiv.2410.00416). URL: <https://arxiv.org/abs/2410.00416v2>.

*Commentary.*

A continuous algebra map (a,b)↦aP+bA sends the scalar pair exponential to the operator exponential. Hence T(z)=exp(−zA), T(0)=I and T(z+w)=T(z)T(w). The operator-valued function is entire with derivative −A at zero. Orthogonal Pythagoras gives ‖T(z)‖≤1 whenever Re z≥0. The actual representative is e^(−z)f(x)+(1−e^(−z))3x∫yf(y)dmu(y). For real t≥0 this preserves the real positive cone and has uniform actual L∞ bound 3/2.

**Definition 1.7 (The source inner-product convention).**

$$\forall B: \operatorname{CLM}\left(\mathbb{C}, H, H\right), \forall u: H, \forall v: H, \operatorname{form}\left(B, u, v\right) = \operatorname{innerC}\left(v, \operatorname{apply}\left(B, u\right)\right)$$

*Formalization.* `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.form` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. Madou; I. Remizov; M. Vafadar (eds.) (2024). *Open problems in one-parameter operator semigroups theory*. DOI: [10.48550/arXiv.2410.00416](https://doi.org/10.48550/arXiv.2410.00416). URL: <https://arxiv.org/abs/2410.00416v2>.

*Commentary.*

For any bounded complex linear B, form B u v is ⟨v,Bu⟩ in Lean's convention. Thus it is linear in u and conjugate-linear in v, as in the source's ⟨Bu,v⟩ convention. Its domain is the full Hilbert space. The association condition tested in claim characterizes w=Bu by form B u v=⟨v,w⟩ for every v.

**Definition 1.8 (The actual form norm).**

$$\forall B: \operatorname{CLM}\left(\mathbb{C}, H, H\right), \forall u: H, \operatorname{formNorm}\left(B, u\right) = \operatorname{sqrt}\left(\operatorname{norm}\left(u\right)^{2} + \operatorname{re}\left(\operatorname{form}\left(B, u, u\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.formNorm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. Madou; I. Remizov; M. Vafadar (eds.) (2024). *Open problems in one-parameter operator semigroups theory*. DOI: [10.48550/arXiv.2410.00416](https://doi.org/10.48550/arXiv.2410.00416). URL: <https://arxiv.org/abs/2410.00416v2>.

*Commentary.*

For A, the diagonal form is real and nonnegative, and ‖u‖≤formNorm A u≤√2‖u‖. Every form-norm Cauchy sequence converges in that form norm, by completeness of the actual L2 Hilbert norm and these two inequalities. This establishes closedness on the full dense domain; it is not a surrogate for the weighted essential sup norm.

**Definition 1.9 (The source-faithful restricted weight assertion).**

$$(claim) \Leftrightarrow (\forall B: \operatorname{CLM}\left(\mathbb{C}, H, H\right), \forall S: (\mathbb{C})\to \operatorname{CLM}\left(\mathbb{C}, H, H\right), (\operatorname{IsSelfAdjoint}\left(B\right)) \Rightarrow ((\forall u: H, (0 \le \operatorname{re}\left(\operatorname{form}\left(B, u, u\right)\right)) \land (\operatorname{im}\left(\operatorname{form}\left(B, u, u\right)\right) = 0)) \Rightarrow ((\forall u: H, \forall w: H, (\forall v: H, \operatorname{form}\left(B, u, v\right) = \operatorname{innerC}\left(v, w\right)) \Leftrightarrow (w = \operatorname{apply}\left(B, u\right))) \Rightarrow ((\forall u: H, \forall v: H, \forall w: H, \forall c: \mathbb{C}, (\operatorname{form}\left(B, u + v, w\right) = \operatorname{form}\left(B, u, w\right) + \operatorname{form}\left(B, v, w\right)) \land ((\operatorname{form}\left(B, \operatorname{smul}\left(c, u\right), v\right) = c \cdot \operatorname{form}\left(B, u, v\right)) \land ((\operatorname{form}\left(B, u, v + w\right) = \operatorname{form}\left(B, u, v\right) + \operatorname{form}\left(B, u, w\right)) \land (\operatorname{form}\left(B, u, \operatorname{smul}\left(c, v\right)\right) = \operatorname{conj}\left(c\right) \cdot \operatorname{form}\left(B, u, v\right))))) \Rightarrow ((\operatorname{Continuous}\left((p: \operatorname{Prod}\left(H, H\right))\mapsto \operatorname{form}\left(B, \operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right)\right)) \Rightarrow ((\operatorname{Dense}\left(\operatorname{univ}\left(H\right)\right)) \Rightarrow ((\forall s: (\mathbb{N})\to H, (\forall e: \mathbb{R}, (0 < e) \Rightarrow (\exists N: \mathbb{N}, \forall m: \mathbb{N}, (N \le m) \Rightarrow (\forall n: \mathbb{N}, (N \le n) \Rightarrow (\operatorname{formNorm}\left(B, \operatorname{apply}\left(s, m\right) - \operatorname{apply}\left(s, n\right)\right) < e)))) \Rightarrow (\exists u: H, \forall e: \mathbb{R}, (0 < e) \Rightarrow (\exists N: \mathbb{N}, \forall n: \mathbb{N}, (N \le n) \Rightarrow (\operatorname{formNorm}\left(B, \operatorname{apply}\left(s, n\right) - u\right) < e)))) \Rightarrow ((\forall z: \mathbb{C}, \operatorname{apply}\left(S, z\right) = \operatorname{exp}\left(\operatorname{smul}\left(-(z), B\right)\right)) \Rightarrow ((\operatorname{apply}\left(S, 0\right) = I) \Rightarrow ((\forall z: \mathbb{C}, \forall w: \mathbb{C}, \operatorname{apply}\left(S, z + w\right) = \operatorname{apply}\left(S, z\right) \cdot \operatorname{apply}\left(S, w\right)) \Rightarrow ((\forall z: \mathbb{C}, \operatorname{AnalyticAt}\left(\mathbb{C}, S, z\right)) \Rightarrow ((\operatorname{HasDerivAt}\left(S, -(B), 0\right)) \Rightarrow ((\forall z: \mathbb{C}, (0 \le \operatorname{re}\left(z\right)) \Rightarrow (\operatorname{norm}\left(\operatorname{apply}\left(S, z\right)\right) \le 1)) \Rightarrow ((\forall t: \mathbb{R}, (0 \le t) \Rightarrow (\forall f: H, (\operatorname{AE}\left(mu, (x: \mathbb{R})\mapsto (0 \le \operatorname{re}\left(\operatorname{eval}\left(f, x\right)\right)) \land (\operatorname{im}\left(\operatorname{eval}\left(f, x\right)\right) = 0)\right)) \Rightarrow (\operatorname{AE}\left(mu, (x: \mathbb{R})\mapsto (0 \le \operatorname{re}\left(\operatorname{eval}\left(\operatorname{apply}\left(\operatorname{apply}\left(S, \operatorname{ofReal}\left(t\right)\right), f\right), x\right)\right)) \land (\operatorname{im}\left(\operatorname{eval}\left(\operatorname{apply}\left(\operatorname{apply}\left(S, \operatorname{ofReal}\left(t\right)\right), f\right), x\right)\right) = 0)\right)))) \Rightarrow ((\forall t: \mathbb{R}, (0 \le t) \Rightarrow (\forall f: H, (\operatorname{MemLp}\left(f, \infty, mu\right)) \Rightarrow (\operatorname{eLpNorm}\left(\operatorname{apply}\left(\operatorname{apply}\left(S, \operatorname{ofReal}\left(t\right)\right), f\right), \infty, mu\right) \le \operatorname{ofRealENN}\left(\operatorname{divide}\left(3, 2\right)\right) \cdot \operatorname{eLpNorm}\left(f, \infty, mu\right)))) \Rightarrow (\exists g: (\mathbb{R})\to \mathbb{R}, (\operatorname{Measurable}\left(g\right)) \land ((\operatorname{MemLp}\left(g, \infty, mu\right)) \land ((\operatorname{MemLp}\left((x: \mathbb{R})\mapsto \operatorname{inv}\left(\operatorname{apply}\left(g, x\right)\right), \infty, mu\right)) \land ((\operatorname{AE}\left(mu, (x: \mathbb{R})\mapsto 0 < \operatorname{apply}\left(g, x\right)\right)) \land (\forall t: \mathbb{R}, (0 \le t) \Rightarrow (\forall f: H, (\operatorname{MemLp}\left(f, \infty, mu\right)) \Rightarrow (\operatorname{eLpNorm}\left((x: \mathbb{R})\mapsto \operatorname{ofReal}\left(\operatorname{apply}\left(g, x\right)\right) \cdot \operatorname{eval}\left(\operatorname{apply}\left(\operatorname{apply}\left(S, \operatorname{ofReal}\left(t\right)\right), f\right), x\right), \infty, mu\right) \le \operatorname{eLpNorm}\left((x: \mathbb{R})\mapsto \operatorname{ofReal}\left(\operatorname{apply}\left(g, x\right)\right) \cdot \operatorname{eval}\left(f, x\right), \infty, mu\right)))))))))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* F. Madou; I. Remizov; M. Vafadar (eds.) (2024). *Open problems in one-parameter operator semigroups theory*. DOI: [10.48550/arXiv.2410.00416](https://doi.org/10.48550/arXiv.2410.00416). URL: <https://arxiv.org/abs/2410.00416v2>.

*Commentary.*

The displayed implications state, in order: bounded self-adjoint B; angle-zero sectoriality; association of B to its full-domain form; sesquilinearity; continuity; density; completeness in the actual form norm; the operator exponential formula; the identity at zero and semigroup law; entire analyticity and generator derivative; right-half-plane operator contractivity; positivity on real nonnegative representatives; the uniform 3/2 actual L∞ bound. The conclusion quantifies a measurable real positive weight and its bounded reciprocal, and all real times and complex inputs in L²∩L∞. AE denotes mu-almost-everywhere; Linf(f) means the actual eLpNorm f infinity mu, not a newly defined scalar norm. CLM means bounded complex linear maps; innerC is Lean's complex inner product; eval selects an actual AE representative; MemLp uses the same mu.

**Theorem 1.10 (No equivalent positive weight contracts this positive semigroup).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* F. Madou; I. Remizov; M. Vafadar (eds.) (2024). *Open problems in one-parameter operator semigroups theory*. DOI: [10.48550/arXiv.2410.00416](https://doi.org/10.48550/arXiv.2410.00416). URL: <https://arxiv.org/abs/2410.00416v2>.

*Commentary.*

The proof supplies B=A and S=T and discharges every form and semigroup premise in Lean. Suppose a weight existed and put w=1/g. Finite measure and essential boundedness put this real positive test function into the actual complex L²∩L∞. The weighted input is one almost everywhere. The actual eLpNorm bound at the single time t=1 gives T(1)w≤w. The representative formula and 1−e^(−1)>0 imply Pw≤w. The integral of x(w−Pw) vanishes because ∫x²=1/3; its integrand is nonnegative. The existing integral-zero criterion and x>0 almost everywhere give w=Pw=cx almost everywhere. Boundedness of g gives w a positive essential lower bound epsilon. For arbitrary real c and epsilon>0 the proof constructs delta=min(1/2,epsilon/(2(|c|+1)))>0. The interval (0,delta) has positive mu measure and satisfies cx<epsilon throughout, contradicting that lower bound. This explicit positive-measure construction is the consumed non-bind escape witness. The faithful-functional rigidity helper is private and consumed by the obstruction; it is not delivered as a standalone wrapper. The remaining helpers organize direct applications of pinned Mathlib and are consumed by this result. The proof uses complex inputs throughout the claim, testing a real positive input only for the contradiction. The positivity restriction is not a separately numbered conjecture in the source. Novelty and priority outside the checked sources remain ASSUMED-UNVERIFIED. The existing damped rotating counterexample retains its separate attribution.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.A`
- Truth anchor: `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.H`
- Truth anchor: `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.P`
- Truth anchor: `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.T`
- Truth anchor: `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.claim`
- Truth anchor: `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.form`
- Truth anchor: `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.formNorm`
- Truth anchor: `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.h`
- Truth anchor: `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.result`
- Truth anchor: `D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.μ`
