# Whole-source coherent amplification

## Abstract

Uniform coherent rotation and an exact finite auxiliary-coin amplification circuit.

Let S and L be arbitrary finite complex coordinate spaces, J an initialization isometry from S to L, C a supplied unitary on L, and P a self-adjoint idempotent good projection. Put U=CJ and suppose (PU)* PU=pI with 0<p<=1. For 0<p<1, Define W=PU/sqrt(p), B=(I-P)U/sqrt(1-p), theta=arcsin(sqrt(p)), and Q=(2UU*-I)(I-2P). The same Q acts on every source column; no unknown input state specifies a reflection.

**Theorem 1.1 (Every power rotates the entire source).**

Lean statement: `D5/S3/Quantum/Recovery/CoherentUniformAmplification.uniform_operator_rotation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/CoherentUniformAmplification.uniform_operator_rotation` (`✓ std3`). ∎

*Citation.* Gilles Brassard; Peter Høyer; Michele Mosca; Alain Tapp (2002). *Quantum Amplitude Amplification and Estimation*. URL: <https://arxiv.org/abs/quant-ph/0005055>.

*Commentary.*

At p=1, U=W already. For 0<p<1, the operators W and B satisfy W*W=B*B=I and W*B=0. For every natural n, Q^n U=sin((2n+1)theta)W+cos((2n+1)theta)B. This is an equality of rectangular operators on the whole source, derived from the scalar success Gram. Induction proves the identity for all powers after the two reflections are evaluated on the two isometric ranges.

For any reference index type and any reference matrix R, tensoring the same identity with R preserves it. In particular, R=I preserves every joint source-reference vector and its density matrix, including entangled inputs. The statement uses no input-dependent choice of plane.

This result is the uniform rotation mechanism of standard amplitude amplification. The finite auxiliary-coin construction below supplies the exact iteration choice and source-query bound. Coherent access to C and its inverse, both subspace reflections, and exact known coin rotations must be supplied; a destructive measurement interface does not supply them. Filter, reflection, and coin compilation costs are not included in a query count.

**Theorem 1.2 (A finite word with exact success on every source input).**

Lean statement: `D5/S3/Quantum/Recovery/CoherentUniformAmplification.exact_coherent_amplification`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/CoherentUniformAmplification.exact_coherent_amplification` (`✓ std3`). ∎

*Citation.* Gilles Brassard; Peter Høyer; Michele Mosca; Alain Tapp (2002). *Quantum Amplitude Amplification and Estimation*. URL: <https://arxiv.org/abs/quant-ph/0005055>.

*Commentary.*

Use the enlarged native ambient L direct-sum L and initialize the coin in its first label: K is the vertical block (J,0). The original operation lifts as diag(C,C). For q in [0,1], the known coin has blocks sqrt(q)I, -sqrt(1-q)I, sqrt(1-q)I, sqrt(q)I. Its adjoint is its inverse. The new good projection is diag(P,0), which requires both the old flag and the first coin label. All failed records remain coherent.

For 0<p<1, choose n=ceil(pi/(4 arcsin(sqrt(p)))-1/2), a=pi/(4n+2), r=sin(a)^2 and q=r/p. The proof establishes 0<r<=p<1, 0<q<=1 and (2n+1)arcsin(sqrt(r))=pi/2. The enlarged prepared success Gram is rI. Its normalized successful isometry is exactly the original W with the fixed first coin label.

Words are written in matrix-product order: the rightmost gate acts first. Each six-gate block is coin, C, initialization reflection, C-adjoint, coin-adjoint, good reflection. The initialization reflection is 2KK*-I and the good reflection is I-2 diag(P,0). Repeat that block n times, followed on the right by coin,C. Evaluation uses only J,C,P,q; W is absent from every gate. Direct reuse of the uniform rotation theorem shows that the evaluated word applied to K is (W,0), with (I-diag(P,0)) times this operator exactly zero. The evaluated operator is unitary on the entire enlarged ambient space. Tensoring with every reference matrix preserves the source equality.

The word contains exactly 2n+1 original C or C-adjoint calls and satisfies 2n+1 <= (pi/2+2)/sqrt(p). When p=1, the word is just the lifted original C and uses one source call. This is the standard known-probability BHMT attenuation method; no algorithmic novelty is claimed. Exact real-angle coin rotations, coherent reversible source access and the two fixed subspace reflections are resources. No destructive measurement, reset, retry, unknown-input reflection or finite discrete-gate compilation is assumed. Filter, reflection and coin compilation costs are outside this source-query bound. The Petz-specific substitution and the passage from an isometry to a channel after discarding its environment are not separate channel theorems here.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/CoherentUniformAmplification.exact_coherent_amplification`
- Truth anchor: `D5/S3/Quantum/Recovery/CoherentUniformAmplification.uniform_operator_rotation`
