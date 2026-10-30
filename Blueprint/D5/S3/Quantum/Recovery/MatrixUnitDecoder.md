# MatrixUnitDecoder

## Abstract

Actual matrix units construct the full decoder without a syndrome basis. Its trace-pairing formula recovers supported commutant-weighted logical matrices. No global bundle or Chern-number claim is made.

ST40.3 application to the actual smooth channel. Take the finite complex channel family N from WholeSmoothRecovery.whole_original_ST37, with its original compact smooth parameter space, complete positivity, trace preservation, CPTP left inverses, constant rank k d, and d>0. Along a path gamma, set Qenc(t)=N(gamma(t))(I), P(t)=spectralSupport(Qenc(t)), W(t)=spectralInverseSqrt(Qenc(t)), pi_t(A)=W(t)N(gamma(t))(A)W(t), and F_ij(t)=pi_t(e_ij). Linearity and the finite matrix-unit expansion identify this actual spectral pi_t(A) with representedMatrix(F(t),A) for every complex A; the diagonal sum identifies unitSupport(F(t)) with this actual P(t). The ST37 returned algebra fields give N(gamma(t))(A)=Qenc(t)pi_t(A), commutation, multiplicativity and adjoints.

Use the actual tangent Dvel of F and K(t)=transportGenerator(F(t),Dvel(t)). On [0,T] with T>=0, assume the original continuity and within-derivative hypotheses. For T>0, MatrixUnitDyson.constructive_transport returns two-sided unitarity of G=dysonSeries(K) and F_ij(t)=G(t)F_ij(0)G(t)†. For T=0 use the actual ambient derivative at zero; MatrixUnitGenerator.generator_from_real_path derives the generator identity from the actual matrix-unit laws, while G(0)=I settles transport. Given the original continuous Hermitian hL and hbar>0, Delta>0, use VL=dysonSeries((-i/hbar)hL) and the literal physical propagator V(t)=G(t)[representedMatrix(F(0),VL(t))+exp(-i Delta t/hbar)(I-unitSupport(F(0)))]. These are the objects in the physical-dynamics application of MatrixUnitDyson; its dynamical proof is reused.

Let Qtilde(t)=G(t)Qenc(0)G(t)†. Complete positivity of the actual N(gamma(0)) makes Qenc(0) positive semidefinite. The ST37 factorization at I and commutation give P(0)Qenc(0)=Qenc(0)P(0)=Qenc(0). Transport and the inverse equations for G therefore give positivity of Qtilde, P(t)Qtilde=Qtilde P(t)=Qtilde, and commutation with every actual F_ij(t). Trace preservation of N(gamma(0)) gives trace(F_vv(0)Qenc(0))=trace(N(gamma(0))(e_vv))=1 for the original reset index v=0; cyclicity and transport give trace(F_vv(t)Qtilde(t))=1. This weight is the transported initial encoding weight; no equality with Qenc(t) is required.

Fix D_t before choosing A: it is exactly ST37's MatrixMap.of_kraus map on the combined decoderKraus(F(t),v,b) and reset matrices e_vb(I-P(t)). ST37 returns complete positivity, trace preservation, and (D_t X)_ij=trace(F_ji(t)X)+trace((I-P(t))X)(e_vv)_ij for every physical X. Transport and trace cyclicity identify D_t(G(t)XG(t)†)=D_0(X) for every X. The supported channel factorization kills both complement cross terms in V(t)N(gamma(0))(A)V(t)†, including the signed phase, and gives the literal output Qtilde(t)pi_t(VL(t)A VL(t)†). Both left and right complement products vanish. Applying the fixed decoder and the actual ST37 recovery field at zero proves D_t(V(t)N(gamma(0))(A)V(t)†)=VL(t)A VL(t)† for every complex logical A and every allowed t. This is a matrix identity, with no density-state restriction, global syndrome frame, physical nonemptiness or full-rank hypothesis; zero complement is included. The full-algebra closed-loop theorem under the same canonical Theta remains a separate application.

**Theorem 1.1 (decoder kraus gram).**

Lean statement: `D5/S3/Quantum/Recovery/MatrixUnitDecoder.decoder_kraus_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/MatrixUnitDecoder.decoder_kraus_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Cédric Bény and Achim Kempf and David W. Kribs (2007). *Quantum Error Correction of Observables*. DOI: [10.1103/PhysRevA.76.042303](https://doi.org/10.1103/PhysRevA.76.042303).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

Actual matrix units construct the full decoder without a syndrome basis. Its trace-pairing formula recovers supported commutant-weighted logical matrices. No global bundle or Chern-number claim is made.

**Theorem 1.2 (decoder trace pairing).**

Lean statement: `D5/S3/Quantum/Recovery/MatrixUnitDecoder.decoder_trace_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/MatrixUnitDecoder.decoder_trace_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Cédric Bény and Achim Kempf and David W. Kribs (2007). *Quantum Error Correction of Observables*. DOI: [10.1103/PhysRevA.76.042303](https://doi.org/10.1103/PhysRevA.76.042303).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

Actual matrix units construct the full decoder without a syndrome basis. Its trace-pairing formula recovers supported commutant-weighted logical matrices. No global bundle or Chern-number claim is made.

**Theorem 1.3 (matrix unit decoder channel).**

Lean statement: `D5/S3/Quantum/Recovery/MatrixUnitDecoder.matrix_unit_decoder_channel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/MatrixUnitDecoder.matrix_unit_decoder_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Cédric Bény and Achim Kempf and David W. Kribs (2007). *Quantum Error Correction of Observables*. DOI: [10.1103/PhysRevA.76.042303](https://doi.org/10.1103/PhysRevA.76.042303).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

Actual matrix units construct the full decoder without a syndrome basis. Its trace-pairing formula recovers supported commutant-weighted logical matrices. No global bundle or Chern-number claim is made.

**Theorem 1.4 (represented matrix mul).**

Lean statement: `D5/S3/Quantum/Recovery/MatrixUnitDecoder.represented_matrix_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/MatrixUnitDecoder.represented_matrix_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Cédric Bény and Achim Kempf and David W. Kribs (2007). *Quantum Error Correction of Observables*. DOI: [10.1103/PhysRevA.76.042303](https://doi.org/10.1103/PhysRevA.76.042303).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

Actual matrix units construct the full decoder without a syndrome basis. Its trace-pairing formula recovers supported commutant-weighted logical matrices. No global bundle or Chern-number claim is made.

**Theorem 1.5 (decoder recovers commutant weight).**

Lean statement: `D5/S3/Quantum/Recovery/MatrixUnitDecoder.decoder_recovers_commutant_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/MatrixUnitDecoder.decoder_recovers_commutant_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Cédric Bény and Achim Kempf and David W. Kribs (2007). *Quantum Error Correction of Observables*. DOI: [10.1103/PhysRevA.76.042303](https://doi.org/10.1103/PhysRevA.76.042303).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

Actual matrix units construct the full decoder without a syndrome basis. Its trace-pairing formula recovers supported commutant-weighted logical matrices. No global bundle or Chern-number claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/MatrixUnitDecoder.decoder_kraus_gram`
- Truth anchor: `D5/S3/Quantum/Recovery/MatrixUnitDecoder.decoder_recovers_commutant_weight`
- Truth anchor: `D5/S3/Quantum/Recovery/MatrixUnitDecoder.decoder_trace_pairing`
- Truth anchor: `D5/S3/Quantum/Recovery/MatrixUnitDecoder.matrix_unit_decoder_channel`
- Truth anchor: `D5/S3/Quantum/Recovery/MatrixUnitDecoder.represented_matrix_mul`
- Dependency: [D5/S3/Quantum/Recovery/KrausCompletion](KrausCompletion.md)
