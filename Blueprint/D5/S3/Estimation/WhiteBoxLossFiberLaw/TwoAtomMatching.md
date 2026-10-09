# Quantitative Two-Atom Matching

## Abstract

Near-radial nonnegative coding costs force simultaneous dictionary matching.

The ambient space is any real inner-product space, including every finite Euclidean space. D is an ordered pair of unit vectors; c has two nonnegative real entries. C(x,D) is the infimum of norm(x-Dc)^2/2+lambda(c0+c1). No independence, distinctness or plane restriction is imposed on the dictionary atoms.

The radial floor lambda norm(x) minus lambda squared over two comes from the Euclidean-norm proximal formula in Parikh and Boyd, Proximal Algorithms, Section 6.5.1. The two-atom zero-weight merging result has a precedent in the Positive-penalty merging proposition of the MAIS-A3 research draft, recorded in mais2026superposition; that source is not peer reviewed. The formulations here use arbitrary real inner-product spaces and allow the amplitude and regularization ranges stated separately below. The quantitative contribution is a simultaneous match for the same dictionary with an explicit positive gap, followed by uniform localization of every small positive-weight minimizer.

**Theorem 1.1 (Square completion).**

$$E ( n e , D , c ) - ( \lambda n - \frac {\lambda ^ {2}} {2} ) = \frac {\Vert ( n - \lambda ) e - D c \Vert ^ {2}} {2} + \lambda \sum _ {i} c _ {i} ( 1 - \langle e , d _ {i} \rangle )$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.code_energy_excess_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Neal Parikh; Stephen Boyd (2014). *Proximal Algorithms*. DOI: [10.1561/2400000003](https://doi.org/10.1561/2400000003).

*Commentary.*

For any real amplitude n and regularization parameter lambda, any unit direction e, any ordered unit dictionary D and any two-coordinate real code c, the energy excess over lambda n minus lambda squared over two equals the displayed squared residual and correlation-defect sum. No positivity assumption is needed for this identity. This square-completion decomposition exposes the correlation defects behind the classical proximal radial floor and supplies the directional estimates below.

**Theorem 1.2 (Pointwise radial lower bound).**

$$( \lambda n - \frac {\lambda ^ {2}} {2} ) \le E ( n e , D , c )$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.feasible_code_energy_lower_bound` (`✓ std3`). ∎

*Citation.* Neal Parikh; Stephen Boyd (2014). *Proximal Algorithms*. DOI: [10.1561/2400000003](https://doi.org/10.1561/2400000003).

*Commentary.*

For every real amplitude n, unit direction e, ordered unit dictionary D, nonnegative lambda and coordinatewise nonnegative code c, the radial baseline is at most the code energy. Each directional defect is nonnegative by Cauchy-Schwarz. The known core is the radial inequality underlying Parikh and Boyd's proximal formula; its pointwise form here also allows arbitrary real amplitudes, lambda=0 and any real inner-product space.

**Theorem 1.3 (Infimal radial lower bound).**

$$( \lambda n - \frac {\lambda ^ {2}} {2} ) \le C ( n e , D )$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.code_cost_radial_lower_bound` (`✓ std3`). ∎

*Citation.* Neal Parikh; Stephen Boyd (2014). *Proximal Algorithms*. DOI: [10.1561/2400000003](https://doi.org/10.1561/2400000003).

*Commentary.*

For every real amplitude n, unit direction e, ordered unit dictionary D and nonnegative lambda, taking the infimum over all coordinatewise nonnegative codes preserves the radial floor. The zero code supplies a nonempty family. For a nonzero signal x, set n to its norm and e to x divided by its norm. For n>lambda>0 this is the classical proximal radial lower bound of Parikh and Boyd, Section 6.5.1; the present statement retains the same floor for all real n and lambda>=0 in arbitrary real inner-product spaces, without asserting attainment.

**Theorem 1.4 (Separated directions occupy different slots).**

$$2 \delta \le dist ( u , w ) , \exists i , dist ( d _ {i} , u ) < \delta , \exists i , dist ( d _ {i} , w ) < \delta \Rightarrow ( dist ( d _ {0} , u ) < \delta \land dist ( d _ {1} , w ) < \delta ) \lor ( dist ( d _ {0} , w ) < \delta \land dist ( d _ {1} , u ) < \delta )$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.two_slot_matching_from_separate_witnesses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In any pseudometric space, for any ordered two-entry map D, targets u and w and real tolerance delta, separation by at least twice delta and one nearby entry for each target imply simultaneous matching in the identity or swapped order. The triangle inequality excludes using the same slot for both targets.

**Theorem 1.5 (Quantitative simultaneous matching).**

$$a C ( n u , D ) + b C ( m w , D ) < a ( \lambda n - \frac {\lambda ^ {2}} {2} ) + b ( \lambda m - \frac {\lambda ^ {2}} {2} ) + \min ( a g ( n , \delta ) , b g ( m , \delta ) ) \Rightarrow ( dist ( d _ {0} , u ) < \delta \land dist ( d _ {1} , w ) < \delta ) \lor ( dist ( d _ {0} , w ) < \delta \land dist ( d _ {1} , u ) < \delta )$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.quantitative_two_slot_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Neal Parikh; Stephen Boyd (2014). *Proximal Algorithms*. DOI: [10.1561/2400000003](https://doi.org/10.1561/2400000003).

*Commentary.*

For arbitrary unit directions u and w in a real inner-product space, positive lambda, amplitudes n and m greater than lambda, positive weights a and b, positive delta and target distance at least twice delta, the displayed strict cost bound forces both slots of the same dictionary to match the two directions. Here g(n,delta) is min((n-lambda)^2/8, lambda(n-lambda)delta^2/4). Square completion bounds the residual, which forces code mass above (n-lambda)/2; atoms all outside the direction ball would then contribute too much correlation defect. Applying this single-direction estimate to each sample and excluding a shared slot yields the simultaneous matching relation. This quantitative two-direction extension uses the classical radial floor but supplies a dictionary-independent gap and a match for both columns.

**Theorem 1.6 (Equality detects an aligned atom).**

$$C ( n e , D ) = ( \lambda n - \frac {\lambda ^ {2}} {2} ) \iff \exists i , d _ {i} = e$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.code_cost_eq_radial_iff` (`✓ std3`). ∎

*Citation.* Neal Parikh; Stephen Boyd (2014). *Proximal Algorithms*. DOI: [10.1561/2400000003](https://doi.org/10.1561/2400000003).

*Commentary.*

For every unit direction e, ordered unit dictionary D, positive lambda and n greater than lambda, equality in the actual infimal radial cost holds exactly when one dictionary atom equals e. The radial value and aligned soft-threshold coefficient are the known proximal core of Parikh and Boyd, Section 6.5.1; the dictionary-level iff corresponds to the alignment criterion of the fiber-law volume's Lemma 4.1, here in an arbitrary real inner-product space. Necessity uses the positive minimum of the two atom distances and the single-direction near-radial estimate; sufficiency uses the single active coefficient n-lambda. This argument does not use simultaneous two-slot matching. It gives the radial equality criterion for every nonzero x with lambda less than its norm.

**Theorem 1.7 (Orthogonal samples and an explicit positive gap).**

$$0 < kappa ( \delta ) \land ( J _ {0} ( D ) < B + kappa ( \delta ) \Rightarrow ( dist ( d _ {0} , u ) < \delta \land dist ( d _ {1} , w ) < \delta ) \lor ( dist ( d _ {0} , w ) < \delta \land dist ( d _ {1} , u ) < \delta ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.whitebox_quantitative_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Neal Parikh; Stephen Boyd (2014). *Proximal Algorithms*. DOI: [10.1561/2400000003](https://doi.org/10.1561/2400000003).

*Acknowledgement.* Claude Fable 5 (audited by GPT 5.6 Sol); repository maintained by Lionel Levine (2026). *The geometry and identifiability of superposition (MAIS-A3 research draft)*. URL: <https://github.com/lionellevine/MAIS>.

*Commentary.*

Let u and v be orthogonal unit vectors, w=(u+v)/sqrt(2), zero-weight objective J0=a C(u,D)+b C(u+v,D), and B=a(lambda-lambda^2/2)+b(sqrt(2)lambda-lambda^2/2). For 0<lambda<1/sqrt(2), a,b>0 and 0<delta<norm(u-w)/2, kappa(delta)=min(a g(1,delta),b g(sqrt(2),delta)) is positive. Every ordered unit dictionary with J0<B+kappa(delta) has both atoms within delta of u and w, in one of the two orders. Repeated, antipodal and off-plane atoms are included in the domain. The baseline uses the classical proximal radial values; the explicit positive kappa and simultaneous matching strengthen the zero-weight merging characterization recorded in MAIS-A3.

**Theorem 1.8 (Uniform perturbation bound).**

$$J _ {0} ( D ) \le J _ {t} ( D ) \le J _ {0} ( D ) + \frac {t} {2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.perturbation_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real weights a and b, any u, unit v, ordered unit dictionary D, lambda>=0 and t>=0, J0(D)<=Jt(D)<=J0(D)+t/2. Nonnegativity of the code energy gives the lower bound, and the zero code gives C(v,D)<=1/2.

**Theorem 1.9 (The exact unperturbed minima).**

$$B \le J _ {0} ( D ) \land ( J _ {0} ( D ) = B \iff ( d _ {0} = u \land d _ {1} = w ) \lor ( d _ {0} = w \land d _ {1} = u ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.zero_global_minima` (`✓ std3`). ∎

*Citation.* Claude Fable 5 (audited by GPT 5.6 Sol); repository maintained by Lionel Levine (2026). *The geometry and identifiability of superposition (MAIS-A3 research draft)*. URL: <https://github.com/lionellevine/MAIS>.

*Commentary.*

For orthogonal unit u and v, 0<lambda<1/sqrt(2) and a,b>0, every ordered unit dictionary has J0 at least B. Equality holds precisely at the ordered dictionaries (u,w) and (w,u), where w=(u+v)/sqrt(2). The canonical dictionary realizes B, so these are exactly the global minimizers. This is the two-atom zero-weight merging core attested by the Positive-penalty merging proposition of MAIS-A3, a research draft, expressed here for arbitrary real inner-product spaces and the stated penalty range. Positive weights force both radial terms to attain equality; the single-direction equality criterion identifies each aligned atom, and distinctness forces different slots. The proof uses that criterion and its single-direction estimate, without invoking the simultaneous near-equality matching theorem.

**Theorem 1.10 (All small positive-weight minimizers localize).**

$$\forall \delta > 0 , \exists eta > 0 , \forall t , 0 < t < eta \Rightarrow argmin ( J _ {t} , D ) \Rightarrow ( dist ( d _ {0} , u ) < \delta \land dist ( d _ {1} , w ) < \delta ) \lor ( dist ( d _ {0} , w ) < \delta \land dist ( d _ {1} , u ) < \delta )$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.small_positive_minimizers_localize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Neal Parikh; Stephen Boyd (2014). *Proximal Algorithms*. DOI: [10.1561/2400000003](https://doi.org/10.1561/2400000003).

*Acknowledgement.* Claude Fable 5 (audited by GPT 5.6 Sol); repository maintained by Lionel Levine (2026). *The geometry and identifiability of superposition (MAIS-A3 research draft)*. URL: <https://github.com/lionellevine/MAIS>.

*Commentary.*

For orthogonal unit u and v, 0<lambda<1/sqrt(2), positive a,b and a+b<1, every positive tolerance delta admits eta>0 such that for every 0<t<eta and every ordered unit dictionary D minimizing Jt over all ordered unit dictionaries, D lies within delta of (u,w) or (w,u). One may take epsilon=min(delta,norm(u-w)/4) and eta=min(kappa(epsilon),1-a-b). Comparing with the canonical dictionary gives J0(D)<=B+t/2, so the simultaneous quantitative matching theorem applies. This extends the literature-attested zero-weight merging core to uniform localization for small positive weights through the explicit matching gap. It is a universal statement about every minimizer and does not assert existence for t>0.

## References

- Truth anchor: `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.code_cost_eq_radial_iff`
- Truth anchor: `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.code_cost_radial_lower_bound`
- Truth anchor: `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.code_energy_excess_eq`
- Truth anchor: `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.feasible_code_energy_lower_bound`
- Truth anchor: `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.perturbation_bounds`
- Truth anchor: `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.quantitative_two_slot_matching`
- Truth anchor: `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.small_positive_minimizers_localize`
- Truth anchor: `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.two_slot_matching_from_separate_witnesses`
- Truth anchor: `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.whitebox_quantitative_matching`
- Truth anchor: `D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching.zero_global_minima`
