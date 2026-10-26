# LaguerreMoments

## Abstract

LaguerreMoments for the strong-absorption cumulant expansion.

Natural-number subtraction is truncated. Unmarked integrals use volume; real-number powers and division use the real field.

**Definition 1.1 (deltaSq).**

$$\forall (M : \mathbb{N}) , \forall (x : Fin M \to \mathbb{R}) , deltaSq M x = (\prod i , \prod j , if i < j then  (x i - x j)^{2} else 1)$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.deltaSq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The squared Vandermonde product.

**Definition 1.2 (deltaPoly).**

$$\forall (M : \mathbb{N}) , deltaPoly M = (\prod i , \prod j , if i < j then  (\operatorname{MvPolynomial}.\operatorname{X} i - \operatorname{MvPolynomial}.\operatorname{X} j)^{2} else 1)$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.deltaPoly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Definition 1.3 (expJet).**

$$\forall (K : \mathbb{R} \to \mathbb{R}) , \forall (r : \mathbb{N}) , expJet K r = (iteratedDeriv r (fun t \mapsto \operatorname{Real}.\operatorname{exp} (K t)) 0)$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.expJet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Definition 1.4 (correctionJet).**

$$\forall (K : \mathbb{R} \to \mathbb{R}) , \forall (B : \mathbb{R} \to \mathbb{R}) , \forall (r : \mathbb{N}) , correctionJet K B r = (iteratedDeriv r (fun t \mapsto \operatorname{Real}.\operatorname{exp} (K t) \cdot B t) 0)$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.correctionJet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Theorem 1.5 (exp_deriv_near).**

$$\forall (K : \mathbb{R} \to \mathbb{R}) , (AnalyticAt \mathbb{R} K 0) \to deriv (fun t \mapsto \operatorname{Real}.\operatorname{exp} (K t)) =^{f} [nhds 0] (fun t \mapsto deriv K t \cdot \operatorname{Real}.\operatorname{exp} (K t))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.exp_deriv_near` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Definition 1.6 (laguerreWeight).**

$$\forall (M : \mathbb{N}) , \forall (a : \mathbb{R}) , \forall (x : Fin M \to \mathbb{R}) , laguerreWeight M a x = (if \forall i , 0 \le x i then \operatorname{Real}.\operatorname{exp} (- a \cdot \sum i , x i) \cdot deltaSq M x else 0)$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Theorem 1.7 (deltaPoly_eval).**

$$\forall (M : \mathbb{N}) , \forall (x : Fin M \to \mathbb{R}) , \operatorname{MvPolynomial}.\operatorname{eval} x (deltaPoly M) = deltaSq M x$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.deltaPoly_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.8 (deltaSq_nonneg).**

$$\forall (M : \mathbb{N}) , \forall (x : Fin M \to \mathbb{R}) , 0 \le deltaSq M x$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.deltaSq_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.9 (exp_jet_recurrence).**

$$\forall (K : \mathbb{R} \to \mathbb{R}) , \forall (n : \mathbb{N}) , (AnalyticAt \mathbb{R} K 0) \to (K 0 = 0) \to iteratedDeriv (n + 1) K 0 = expJet K (n + 1) - \sum i \in range n , (\operatorname{n}.\operatorname{choose} i : \mathbb{R}) \cdot iteratedDeriv (i + 1) K 0 \cdot expJet K (n - i)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.exp_jet_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.10 (gammaCGF_analytic).**

$$\forall (d : \mathbb{R}) , AnalyticAt \mathbb{R} (gammaCGF d) 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.gammaCGF_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.11 (correctionCGF_analytic).**

$$\forall (d : \mathbb{R}) , AnalyticAt \mathbb{R} (correctionCGF d) 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.correctionCGF_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.12 (FirstOrder.congr_eventually).**

$$\forall (f : \mathbb{R} \to \mathbb{R}) , \forall (g : \mathbb{R} \to \mathbb{R}) , \forall (a : \mathbb{R}) , \forall (b : \mathbb{R}) , (FirstOrder f a b) \to (f =^{f} [atTop] g) \to FirstOrder g a b$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.congr_eventually` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Definition 1.13 (partition).**

$$\forall (M : \mathbb{N}) , \forall (a : \mathbb{R}) , partition M a = (\int x , laguerreWeight M a x)$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.partition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integral of the Laguerre weight on the nonnegative orthant.

**Theorem 1.14 (laguerreWeight_integrable).**

$$\forall (M : \mathbb{N}) , \forall (a : \mathbb{R}) , (0 < a) \to Integrable (laguerreWeight M a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreWeight_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.15 (laguerreWeight_nonneg).**

$$\forall (M : \mathbb{N}) , \forall (a : \mathbb{R}) , \forall (x : Fin M \to \mathbb{R}) , 0 \le laguerreWeight M a x$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreWeight_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.16 (laguerrePolynomial_integrable).**

$$\forall (M : \mathbb{N}) , \forall (a : \mathbb{R}) , \forall (P : MvPolynomial (Fin M) \mathbb{R}) , (0 < a) \to Integrable (fun x \mapsto laguerreWeight M a x \cdot eval x P)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerrePolynomial_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.17 (singleWPoly_eval).**

$$\forall (M : \mathbb{N}) , \forall (x : Fin M \to \mathbb{R}) , eval x (\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} (fun i : Fin M \mapsto ((X i)^{2} : MvPolynomial (Fin M) \mathbb{R}))) = (\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} (fun i \mapsto  (x i)^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.singleWPoly_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.18 (correction_jet_recurrence).**

$$\forall (K : \mathbb{R} \to \mathbb{R}) , \forall (B : \mathbb{R} \to \mathbb{R}) , \forall (n : \mathbb{N}) , (AnalyticAt \mathbb{R} K 0) \to (AnalyticAt \mathbb{R} B 0) \to (K 0 = 0) \to (B 0 = 0) \to iteratedDeriv (n + 1) B 0 = correctionJet K B (n + 1) - \sum i \in range n , (\operatorname{n}.\operatorname{choose} i : \mathbb{R}) \cdot (iteratedDeriv (i + 1) K 0 \cdot correctionJet K B (n - i) + iteratedDeriv (i + 1) B 0 \cdot expJet K (n - i))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.correction_jet_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.19 (partition_pos).**

$$\forall (M : \mathbb{N}) , \forall (a : \mathbb{R}) , (0 < a) \to 0 < partition M a$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.partition_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Definition 1.20 (laguerreMoment).**

$$\forall (M : \mathbb{N}) , \forall (r : \mathbb{N}) , \forall (a : \mathbb{R}) , laguerreMoment M r a = ((\int x , (\sum i : Fin M ,  (x i)^{r}) \cdot laguerreWeight M a x) / partition M a)$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Definition 1.21 (laguerreWeightedMeasure).**

$$\forall (M : \mathbb{N}) , \forall (Q : MvPolynomial (Fin M) \mathbb{R}) , laguerreWeightedMeasure M Q = ((\operatorname{ENNReal}.\operatorname{ofReal} (partition M M))^{-1} \cdot \operatorname{volume}.\operatorname{withDensity} (fun x \mapsto \operatorname{ENNReal}.\operatorname{ofReal} (laguerreWeight M M x \cdot eval x Q)))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreWeightedMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Theorem 1.22 (singleWPoly_nonneg).**

$$\forall (M : \mathbb{N}) , \forall (x : Fin M \to \mathbb{R}) , 0 \le eval x (\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} (fun i : Fin M \mapsto ((X i)^{2} : MvPolynomial (Fin M) \mathbb{R})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.singleWPoly_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Definition 1.23 (laguerreH).**

$$\forall (M : \mathbb{N}) , laguerreH M = (mgf ((fun x : Fin M \to \mathbb{R} \mapsto \operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} x)) (laguerreWeightedMeasure M 1))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreH` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Definition 1.24 (laguerreHw).**

$$\forall (M : \mathbb{N}) , laguerreHw M = (mgf ((fun x : Fin M \to \mathbb{R} \mapsto \operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} x)) (laguerreWeightedMeasure M (\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} (fun i : Fin M \mapsto ((X i)^{2} : MvPolynomial (Fin M) \mathbb{R})))))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreHw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed definition is used in the moment and density expansions.

**Theorem 1.25 (cumulant_expansion_of_moments).**

$$\forall (m : \mathbb{N} \to \mathbb{R} \to \mathbb{R}) , \forall (k : \mathbb{N} \to \mathbb{R} \to \mathbb{R}) , \forall (a : \mathbb{N} \to \mathbb{R}) , \forall (b : \mathbb{N} \to \mathbb{R}) , \forall (c : \mathbb{N} \to \mathbb{R}) , \forall (d : \mathbb{N} \to \mathbb{R}) , (\forall r , FirstOrder (m r) (a r) (b r)) \to (\forall \gamma : \mathbb{R} , 0 < \gamma \to \forall n : \mathbb{N} , k (n + 1) \gamma = m (n + 1) \gamma - \sum i \in range n , (\operatorname{n}.\operatorname{choose} i : \mathbb{R}) \cdot k (i + 1) \gamma \cdot m (n - i) \gamma) \to (\forall n : \mathbb{N} , c (n + 1) = a (n + 1) - \sum i \in range n , (\operatorname{n}.\operatorname{choose} i : \mathbb{R}) \cdot c (i + 1) \cdot a (n - i)) \to (\forall n : \mathbb{N} , d (n + 1) = b (n + 1) - \sum i \in range n , (\operatorname{n}.\operatorname{choose} i : \mathbb{R}) \cdot (c (i + 1) \cdot b (n - i) + d (i + 1) \cdot a (n - i))) \to \forall r : \mathbb{N} , 1 \le r \to FirstOrder (k r) (c r) (d r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.cumulant_expansion_of_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.26 (laguerreWeighted_mgf_derivative).**

$$\forall (M : \mathbb{N}) , \forall (Q : MvPolynomial (Fin M) \mathbb{R}) , \forall (r : \mathbb{N}) , (1 \le M) \to (\forall x , 0 \le eval x Q) \to iteratedDeriv r (mgf ((fun x : Fin M \to \mathbb{R} \mapsto \operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} x)) (laguerreWeightedMeasure M Q)) 0 = (\int x , laguerreWeight M M x \cdot eval x Q \cdot  (\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} x)^{r}) / partition M M$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreWeighted_mgf_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.27 (laguerre_p1).**

$$\forall (M : \mathbb{N}) , \forall (a : \mathbb{R}) , (0 < a) \to laguerreMoment M 1 a =  (M : \mathbb{R})^{2} / a$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerre_p1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.28 (laguerreH_near).**

$$\forall (M : \mathbb{N}) , (1 \le M) \to laguerreH M =^{f} [nhds 0] (fun t \mapsto \operatorname{Real}.\operatorname{exp} (gammaCGF ((M : \mathbb{R})^{2}) t))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreH_near` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.29 (laguerreH_iterated).**

$$\forall (M : \mathbb{N}) , \forall (r : \mathbb{N}) , (1 \le M) \to (\int x , laguerreWeight M M x \cdot  (\operatorname{Finset}.\operatorname{expect} \operatorname{Finset}.\operatorname{univ} x)^{r}) / partition M M = expJet (gammaCGF ((M : \mathbb{R})^{2})) r$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreH_iterated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.30 (laguerreHw_near).**

$$\forall (M : \mathbb{N}) , (1 \le M) \to laguerreHw M =^{f} [nhds 0] (fun t \mapsto 2 \cdot \operatorname{Real}.\operatorname{exp} (gammaCGF ((M : \mathbb{R})^{2}) t) \cdot  (inverseSlope ((M : \mathbb{R})^{2}) t)^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreHw_near` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity or estimate is used in the moment and density expansions.

**Theorem 1.31 (derivation_product_eigen).**

$$\forall (M : (\mathbb{N})) , ((\forall (\sigma : (Type*)) , ((([DecidableEq \sigma]) \to ((\forall (D : (Derivation \mathbb{R} (MvPolynomial (Fin M) \mathbb{R}) (MvPolynomial (Fin M) \mathbb{R}))) , ((\forall (s : (Finset \sigma)) , ((\forall (f : ((\sigma) \to (MvPolynomial (Fin M) \mathbb{R}))) , ((\forall (g : ((\sigma) \to (MvPolynomial (Fin M) \mathbb{R}))) , ((((\forall i \in s , (D (f i) = g i \cdot f i))) \to ((D (\prod i \in s , f i) = (\sum i \in s , g i) \cdot \prod i \in s , f i))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.derivation_product_eigen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.32 (orthant_measure).**

$$\forall (M : (\mathbb{N})) , (((volume : (Measure ((Fin M) \to (\mathbb{R})))) . restrict ((\operatorname{Set}.\operatorname{Ici} (0 : ((Fin M) \to (\mathbb{R}))))) = orthantMeasure M))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.orthant_measure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.33 (polynomial_exp_integrable_single).**

$$\forall (M : (\mathbb{N})) , ((\forall (a : (\mathbb{R})) , ((((0 < a)) \to ((\forall (P : (MvPolynomial (Fin M) \mathbb{R})) , ((Integrable (fun x \mapsto (\operatorname{Real}.\operatorname{exp} (- a \cdot \sum i , x i) \cdot \operatorname{MvPolynomial}.\operatorname{eval} x P)) (orthantMeasure M)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.polynomial_exp_integrable_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Definition 1.34 (polyIntegral).**

$$\forall (M : (\mathbb{N})) , ((\forall (a : (\mathbb{R})) , ((\forall (P : (MvPolynomial (Fin M) \mathbb{R})) , ((polyIntegral a P = (\int x , \operatorname{Real}.\operatorname{exp} (- a \cdot \sum i , x i) \cdot \operatorname{MvPolynomial}.\operatorname{eval} x P \,d orthantMeasure M)))))))$$

*Formalization.* `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.polyIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.35 (polyIntegral_add).**

$$\forall (M : (\mathbb{N})) , ((\forall (a : (\mathbb{R})) , ((((0 < a)) \to ((\forall (P : (MvPolynomial (Fin M) \mathbb{R})) , ((\forall (Q : (MvPolynomial (Fin M) \mathbb{R})) , ((polyIntegral a (P + Q) = polyIntegral a P + polyIntegral a Q))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.polyIntegral_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.36 (polyIntegral_sum).**

$$\forall (M : (\mathbb{N})) , ((\forall (a : (\mathbb{R})) , ((((0 < a)) \to ((\forall (\sigma : (Type*)) , ((\forall (s : (Finset \sigma)) , ((\forall (P : ((\sigma) \to (MvPolynomial (Fin M) \mathbb{R}))) , ((polyIntegral a (\sum i \in s , P i) = \sum i \in s , polyIntegral a (P i)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.polyIntegral_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.37 (polyIntegral_X_sq).**

$$\forall (M : (\mathbb{N})) , ((\forall (a : (\mathbb{R})) , ((((0 < a)) \to ((\forall (i : (Fin M)) , ((\forall (P : (MvPolynomial (Fin M) \mathbb{R})) , ((a \cdot polyIntegral a (((X i))^{2} \cdot P) = 2 \cdot polyIntegral a (X i \cdot P) + polyIntegral a (((X i))^{2} \cdot \operatorname{MvPolynomial}.\operatorname{pderiv} i P)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.polyIntegral_X_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

**Theorem 1.38 (laguerre_p2).**

$$\forall (M : (\mathbb{N})) , ((\forall (a : (\mathbb{R})) , ((((0 < a)) \to ((laguerreMoment M 2 a = 2 \cdot ((M : (\mathbb{R})))^{3} / (a)^{2}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerre_p2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula relates the polynomial integrals and the normalized finite-channel measure.

## References

- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.congr_eventually`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.correctionCGF_analytic`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.correctionJet`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.correction_jet_recurrence`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.cumulant_expansion_of_moments`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.deltaPoly`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.deltaPoly_eval`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.deltaSq`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.deltaSq_nonneg`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.derivation_product_eigen`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.expJet`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.exp_deriv_near`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.exp_jet_recurrence`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.gammaCGF_analytic`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreH`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreH_iterated`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreH_near`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreHw`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreHw_near`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreMoment`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerrePolynomial_integrable`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreWeight`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreWeight_integrable`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreWeight_nonneg`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreWeightedMeasure`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerreWeighted_mgf_derivative`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerre_p1`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.laguerre_p2`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.orthant_measure`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.partition`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.partition_pos`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.polyIntegral`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.polyIntegral_X_sq`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.polyIntegral_add`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.polyIntegral_sum`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.polynomial_exp_integrable_single`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.singleWPoly_eval`
- Truth anchor: `D5/S3/Quantum/Transport/StrongAbsorption/LaguerreMoments.singleWPoly_nonneg`
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/Foundations](Foundations.md)
