# Attenuator

## Abstract

The full bosonic attenuator and the coherent-state output-entropy question.

The one-mode space is lp(Function.const(Nat,Complex),2) and the two-mode space is lp(Function.const(Nat,lp(Function.const(Nat,Complex),2)),2). The occupation vector at n is lp.single 2 n (Complex.ofReal 1). All state and environment supports are unrestricted. conjStarAlgEquiv is Mathlib LinearIsometryEquiv.conjStarAlgEquiv, mapping T to U composed with T and U inverse. Function names are the displayed Lean definitions or the explicitly stated Mathlib operations. Application parentheses retain grouping; NatSub is truncated natural subtraction, val is the natural value of a finite index, toReal is the natural-to-real cast and Complex.ofReal is the real-to-complex cast. Fields carrying proofs are omitted from constructor formulas; when a named proof parameter occurs in a function signature it appears as an argument of that function.

**Definition 1.1 (ProbabilityVector).**

$$\begin{aligned}\forall p : ProbabilityVector, (\operatorname{weight}\left(p\right):\mathbb{N} \to \mathbb{R})\\\forall p : ProbabilityVector, (\forall n : \mathbb{N}, (0 \le \operatorname{weight}\left(p, n\right)))\\\forall p : ProbabilityVector, (\operatorname{HasSum}\left(\operatorname{weight}\left(p\right), 1\right))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.ProbabilityVector` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The structure has precisely the data field weight: Nat -> Real and proof fields nonneg and normalized displayed as separate rows above; its support is unrestricted.

**Definition 1.2 (DensityOperator).**

$$\begin{aligned}\forall rho : DensityOperator, (\operatorname{operator}\left(rho\right):\operatorname{ContinuousLinearMap}\left(\mathbb{C}, \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right), \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right)\right))\\\forall rho : DensityOperator, (\operatorname{IsPositive}\left(\operatorname{operator}\left(rho\right)\right))\\\forall rho : DensityOperator, (\operatorname{HasSum}\left((n:\mathbb{N})\mapsto(\operatorname{Re}\left(\operatorname{inner}\left(\mathbb{C}, \operatorname{lpsingle}\left(2, n, \operatorname{ComplexofReal}\left(1\right)\right), \operatorname{operator}\left(rho\right)\left(\operatorname{lpsingle}\left(2, n, \operatorname{ComplexofReal}\left(1\right)\right)\right)\right)\right)), 1\right))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.DensityOperator` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The structure has precisely the data field operator and proof fields positive and trace_one displayed as separate rows above. For a positive bounded operator, finite full-basis diagonal sum characterizes trace class. No Fock-diagonality assumption is made on inputs.

**Definition 1.3 (outputVector).**

$$\forall eta : \mathbb{R}, (\forall hEta : eta \in \operatorname{SetIcc}\left(0, 1\right), (\forall p : ProbabilityVector, (\forall rho : DensityOperator, (\forall q : \operatorname{Prod}\left(\mathbb{N}, \operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right)\right), (\operatorname{outputVector}\left(eta, hEta, p, rho, q\right) = \operatorname{smul}\left(\operatorname{ComplexofReal}\left(\operatorname{sqrt}\left(\operatorname{weight}\left(p, \operatorname{fst}\left(q\right)\right)\right)\right), \operatorname{beamSplitter}\left(eta, hEta, \operatorname{tensor}\left(\operatorname{CFCsqrt}\left(\operatorname{operator}\left(rho\right)\right)\left(\operatorname{lpsingle}\left(2, \operatorname{fst}\left(\operatorname{snd}\left(q\right)\right), \operatorname{ComplexofReal}\left(1\right)\right)\right), \operatorname{lpsingle}\left(2, \operatorname{fst}\left(q\right), \operatorname{ComplexofReal}\left(1\right)\right)\right)\right)\left(\operatorname{snd}\left(\operatorname{snd}\left(q\right)\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.outputVector` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

q=(n,m,l) indexes the environment number n, the square-root column m of the input, and the discarded-mode slice l. This is the square-root Kraus realization of Tr_2[U_eta(rho tensor sum_n p_n|n><n|)U_eta^dagger], including off-diagonal inputs.

**Definition 1.4 (attenuatorOperator).**

$$\forall eta : \mathbb{R}, (\forall hEta : eta \in \operatorname{SetIcc}\left(0, 1\right), (\forall p : ProbabilityVector, (\forall rho : DensityOperator, (\operatorname{attenuatorOperator}\left(eta, hEta, p, rho\right) = \operatorname{mixture}\left(\operatorname{Prod}\left(\mathbb{N}, \operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right)\right), (q:\operatorname{Prod}\left(\mathbb{N}, \operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right)\right))\mapsto(\operatorname{outputVector}\left(eta, hEta, p, rho, q\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.attenuatorOperator` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The displayed equation specifies the defining expression.

**Definition 1.5 (attenuator).**

$$\forall eta : \mathbb{R}, (\forall hEta : eta \in \operatorname{SetIcc}\left(0, 1\right), (\forall p : ProbabilityVector, (\forall rho : DensityOperator, (\operatorname{operator}\left(\operatorname{attenuator}\left(eta, hEta, p, rho\right)\right) = \operatorname{attenuatorOperator}\left(eta, hEta, p, rho\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.attenuator` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The state constructor has this operator field. Summability, positivity and trace one of the full triple-index ensemble are checked in Lean.

**Definition 1.6 (pureDensity).**

$$\forall v : \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right), (\forall hv : \left\lVert v \right\rVert = 1, (\operatorname{operator}\left(\operatorname{pureDensity}\left(v, hv\right)\right) = \operatorname{rankOne}\left(\mathbb{C}, v, v\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.pureDensity` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The normalized vector gives its existing Mathlib rank-one projector as the operator field; positivity and trace-one proofs complete the density structure.

**Definition 1.7 (pureOutputVector).**

$$\forall eta : \mathbb{R}, (\forall hEta : eta \in \operatorname{SetIcc}\left(0, 1\right), (\forall p : ProbabilityVector, (\forall v : \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right), (\forall q : \operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right), (\operatorname{pureOutputVector}\left(eta, hEta, p, v, q\right) = \operatorname{smul}\left(\operatorname{ComplexofReal}\left(\operatorname{sqrt}\left(\operatorname{weight}\left(p, \operatorname{fst}\left(q\right)\right)\right)\right), \operatorname{beamSplitter}\left(eta, hEta, \operatorname{tensor}\left(v, \operatorname{lpsingle}\left(2, \operatorname{fst}\left(q\right), \operatorname{ComplexofReal}\left(1\right)\right)\right)\right)\left(\operatorname{snd}\left(q\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.pureOutputVector` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The displayed equation specifies the defining expression.

**Definition 1.8 (pureAttenuatorOperator).**

$$\forall eta : \mathbb{R}, (\forall hEta : eta \in \operatorname{SetIcc}\left(0, 1\right), (\forall p : ProbabilityVector, (\forall v : \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right), (\operatorname{pureAttenuatorOperator}\left(eta, hEta, p, v\right) = \operatorname{mixture}\left(\operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right), (q:\operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right))\mapsto(\operatorname{pureOutputVector}\left(eta, hEta, p, v, q\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.pureAttenuatorOperator` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The pure-input ensemble agrees with the full square-root attenuator. The environment expansion sums p_n times the partial trace of U_eta(v tensor |n>).

**Theorem 1.9 (coherent_output_covariance).**

$$\forall eta : \mathbb{R}, (\forall hEta : eta \in \operatorname{SetIcc}\left(0, 1\right), (\forall p : ProbabilityVector, (\forall alpha : \mathbb{C}, (\operatorname{pureAttenuatorOperator}\left(eta, hEta, p, \operatorname{displacement}\left(alpha, \operatorname{lpsingle}\left(2, 0, \operatorname{ComplexofReal}\left(1\right)\right)\right)\right) = \operatorname{conjStarAlgEquiv}\left(\operatorname{displacement}\left((\operatorname{ComplexofReal}\left(\operatorname{sqrt}\left(eta\right)\right)) \cdot (alpha)\right), \operatorname{pureAttenuatorOperator}\left(eta, hEta, p, \operatorname{lpsingle}\left(2, 0, \operatorname{ComplexofReal}\left(1\right)\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.coherent_output_covariance` (`✓ std3`). ∎

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

For every countably supported phase-invariant environment, every coherent input has a displaced vacuum output. The assertion concerns the full operator, including its coherences.

**Definition 1.10 (coherentDensity).**

$$\forall alpha : \mathbb{C}, (\operatorname{operator}\left(\operatorname{coherentDensity}\left(alpha\right)\right) = \operatorname{rankOne}\left(\mathbb{C}, \operatorname{coherent}\left(alpha\right), \operatorname{coherent}\left(alpha\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.coherentDensity` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The displayed equation specifies the defining expression.

**Definition 1.11 (fockDensity).**

$$\forall n : \mathbb{N}, (\operatorname{operator}\left(\operatorname{fockDensity}\left(n\right)\right) = \operatorname{rankOne}\left(\mathbb{C}, \operatorname{lpsingle}\left(2, n, \operatorname{ComplexofReal}\left(1\right)\right), \operatorname{lpsingle}\left(2, n, \operatorname{ComplexofReal}\left(1\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.fockDensity` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The displayed equation specifies the defining expression.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.DensityOperator`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.ProbabilityVector`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.attenuator`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.attenuatorOperator`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.coherentDensity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.coherent_output_covariance`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.fockDensity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.outputVector`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.pureAttenuatorOperator`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.pureDensity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator.pureOutputVector`
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance](DisplacementCovariance.md)
