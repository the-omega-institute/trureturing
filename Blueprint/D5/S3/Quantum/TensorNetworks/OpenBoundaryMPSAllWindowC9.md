# All adjacent windows on the actual MPS image

## Abstract

Raw all-window recovery and individual-window ambiguity on the actual MPS image

**Theorem 1.1 (One common full-amplitude principal locus).**

$$\forall m \in Nat,\; \exists P \in MvPolynomial\left(Sum\left(Word\left(3 + m\right), Word\left(3 + m\right)\right), Real\right),\; (((((P \neq 0) \land (Nonempty\left(FullPrincipalLocus\left(m, P\right)\right))) \land (IsOpen\left(FullPrincipalLocus\left(m, P\right)\right))) \land (Dense\left(FullPrincipalLocus\left(m, P\right)\right))) \land (\forall psi \in openBoundaryMPS\left(3 + m\right),\; \forall z \in Complex,\; (norm\left(z\right) = 1) \Rightarrow (\exists hz \in Member\left(smul\left(z, psi\right), openBoundaryMPS\left(3 + m\right)\right),\; (Member\left(mk\left(smul\left(z, psi\right), hz\right), FullPrincipalLocus\left(m, P\right)\right)) \Leftrightarrow (Member\left(psi, FullPrincipalLocus\left(m, P\right)\right))))) \land (\forall psi \in openBoundaryMPS\left(3 + m\right),\; (Member\left(psi, FullPrincipalLocus\left(m, P\right)\right)) \Rightarrow ((((psi \neq 0) \land (\forall p \in Nat,\; \forall q \in Nat,\; (p + q = m) \Rightarrow (\forall h \in p + 3 + q = 3 + m,\; \forall phi \in openBoundaryMPS\left(3 + m\right),\; (rawInterior\left(p, 3, q, castState\left(h, phi\right)\right) = rawInterior\left(p, 3, q, castState\left(h, psi\right)\right)) \Leftrightarrow (\exists z \in Complex,\; (norm\left(z\right) = 1) \land (phi = smul\left(z, psi\right)))))) \land (\forall p \in Nat,\; \forall q \in Nat,\; (p + q = m + 1) \Rightarrow (\forall h \in p + 2 + q = 3 + m,\; \exists phi \in openBoundaryMPS\left(3 + m\right),\; ((phi \neq 0) \land (rawInterior\left(p, 2, q, castState\left(h, phi\right)\right) = rawInterior\left(p, 2, q, castState\left(h, psi\right)\right))) \land (\neg (\exists z \in Complex,\; (norm\left(z\right) = 1) \land (phi = smul\left(z, psi\right))))))) \land (\forall p \in Nat,\; \forall q \in Nat,\; (p + q = m + 2) \Rightarrow (\forall h \in p + 1 + q = 3 + m,\; \exists phi \in openBoundaryMPS\left(3 + m\right),\; ((phi \neq 0) \land (rawInterior\left(p, 1, q, castState\left(h, phi\right)\right) = rawInterior\left(p, 1, q, castState\left(h, psi\right)\right))) \land (\neg (\exists z \in Complex,\; (norm\left(z\right) = 1) \land (phi = smul\left(z, psi\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSAllWindowC9.result` (`✓ std3`). ∎

*Resolves.* `Problems/critch-morton-2014-open-boundary-mps-raw-c9` (proved) by `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSAllWindowC9.result` and `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"critch-morton-2014-open-boundary-mps-raw-c9","declaration_gid":"D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSAllWindowC9.result","resolution_kind":"proved"} -->

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"critch-morton-2014-open-boundary-mps-raw-c9","declaration_gid":"D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

In the displayed formula FullPrincipalLocus(m,P) denotes exactly {psi in openBoundaryMPS(3+m) | eval(realCoordinates(psi),P) is nonzero}, mk is the subtype constructor, and amplitudes use their underlying functions. For every natural m, N=3+m, there is one nonzero real polynomial P in ALL real and imaginary amplitude coordinates Word(N) plus Word(N). Its nonvanishing locus G in the ENTIRE literal actual openBoundaryMPS(N) image is nonempty, relatively Euclidean open and dense, and U(1) saturated. Every target in G is nonzero. For EVERY natural p,q with p+q=m and EVERY exact length equality h, equality of that ONE complete raw three-site interior with ANY actual competitor is equivalent to a unit-phase relation. For EVERY p+q=m+1 and h there is a nonzero actual nonphase competitor with the same complete raw two-site window. For EVERY p+q=m+2 and h the same assertion holds for the one-site window. Competitors can depend on the window and have no regularity, chart or genericity premise. No collection of jointly observed windows is assumed.

Write L_R=actualPrincipalLocus(m,R), O=observedPolynomial, and let B be supplied by intrinsic_actual_q2_fiber. T is the intrinsic_interior_recovery polynomial when m>=2 and 1 otherwise; A is the observed_interior_ambiguity polynomial when m>=1 and 1 otherwise. If H is actual-state reversal, G=L_O intersect L_B intersect L_T intersect L_A intersect H inverse(L_O) intersect H inverse(L_B). H is an involutive homeomorphism: reversing the physical word transposes each original core by ORDINARY transpose and swaps the original boundary vectors. No conjugation is used. The finite intersection is dense and open, and has one common ACTUAL witness by successive dense-open intersection. Continuity alone is not used to infer density of a preimage.

For every observed real polynomial R, lift(R) substitutes the COMPLETE Q3 real and imaginary Gram-coordinate polynomials, summing over every exterior word. Its evaluation at any amplitude is exactly R evaluated on the complete raw prefix Q3. Put L=O B T A and R=O B. The literal full-state polynomial is lift(L) times rename(tau,lift(R)), where tau reverses each real and imaginary word coordinate. Evaluation identifies its nonvanishing locus with G. Evaluation at the same common actual witness proves P nonzero; separate witnesses for its factors would not suffice. Public locus_phase and actual_phase give exactly U(1) saturation, without radial invariance.

The original prefix recovery supplies the left Q3. Right recovery reverses the target and arbitrary competitor, applies prefix recovery there, and reverses the phase equation. Strict interior recovery uses intrinsic_interior_recovery unchanged. The original prefix-Q2 fiber is reduced definitionally through its public proposition. Its every-neighborhood clause is specialized to the open NONZERO neighborhood of the explicitly nonzero target. Reversal transports that same actual nonzero nonphase witness at the right boundary. The interior two-site supplier already retains all three properties. Two exact adjacent-pair partial-trace identities, with full exterior bijections and value-preserving length casts, give each one-site witness from a containing pair; they preserve the chosen competitor.

At m=0 (N=3), only the whole-chain Q3 and the two boundary Q2 windows occur, and T=A=1. At m=1 (N=4), both Q3 windows are boundary windows, T=1 and A handles the one internal pair. At m>=2 both internal suppliers apply. Positivity of both exterior lengths forces these thresholds; no supplier is called out of range. Every equality proof h is retained in the result telescope. Word(0) is summed as a singleton, never dropped as an empty exterior.

Critch and Morton, SIGMA 10 (2014), 095, Conjecture 9, provide the original assertion and raw displayed partial trace. This result is a sufficient strengthening of the raw N>=4 prefix recovery and no-fewer formulation to every N>=3 and every placement. N>=3 and the specific real-principal genericity convention are the formal strengthening, not quoted author wording. The reused suppliers include the Ma--Zhang C8 contribution with its license. Word reversal uses GVHunter.reverse_word_list. Within the bounded accessible literature examined, no exact C9 settlement was identified; this does not establish priority or uniqueness.

Unit-phase saturation of this raw locus alone does not justify a dense normalized slice. OpenBoundaryMPSNormalizedC9.result supplies a separately proved dense physical-mass-one slice with both target and competitors normalized for the same physical C9 reading. This result makes no closure-only, exceptional-target, jointly known marginal, stability, dynamics, energy or thermodynamic claim.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSAllWindowC9.result`
- Dependency: [D5/S3/Analytic/Hunter/NCHunterPositivity](../../Analytic/Hunter/NCHunterPositivity.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/InteriorSpectralAmbiguity](InteriorSpectralAmbiguity.md)
