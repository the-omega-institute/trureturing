# A power-mean counterexample in the Euclidean operator norm

## Abstract

An exact positive definite pair violates the p=2 power-mean distance monotonicity in the Euclidean induced operator norm.

Raluca Dumitru and Jose Franco, On the monotonicity of weighted power means of matrices, arXiv:1701.07023v1, Conjecture 9, asks for decreasing distance for every unitarily invariant norm and every 0<p≤2. Version 2 withdraws the preprint because Proposition 4 is false; withdrawal alone does not refute Conjecture 9. The public three-author manuscript of the 2017 successor does not state this exact all-norm assertion. Its p=2 Frobenius and p=1/2 all-unitarily-invariant-norm results are compatible with this counterexample. Publisher full text was not obtained, so no complete version-of-record comparison is claimed. The result here concerns the v1 assertion through its p=2 operator-norm specialization. No exact prior refutation was found in the bounded later primary literature inspected through 2026-11-01; the relevant 2018 The matrix power means and interpolations (DOI 10.15352/aot.1801-1288) remained text-inaccessible, and other candidates were metadata-only. Current-open status, novelty, priority, and uniqueness remain unverified; this component earns zero verified-original or unique credit.

**Definition 1.1 (The p=2 spectral power mean).**

Lean statement: `D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.mu2`

*Formalization.* `D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.mu2` (`✓ std3`).

*Citation.* Raluca Dumitru; Jose Franco (2017). *On the monotonicity of weighted power means of matrices*. URL: <https://arxiv.org/abs/1701.07023v1>.

*Commentary.*

For complex finite square matrices, mu2 A B t is mpow (t • mpow A 2 + (1−t) • mpow B 2) (1/2), using SpectralPower.mpow. For positive semidefinite inputs and t in [0,1], it is the positive spectral square root of tA²+(1−t)B².

**Definition 1.2 (Only the p=2 operator-norm specialization).**

$$claim \Leftrightarrow (\forall n: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall B: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall s: \mathbb{R}, \forall t: \mathbb{R}, ((\operatorname{PosSemidef}\left(A\right)) \land ((\operatorname{PosSemidef}\left(B\right)) \land ((0 \le s) \land ((s \le t) \land (t \le 1))))) \Rightarrow (\operatorname{opnorm}\left(A - \operatorname{mu2}\left(A, B, t\right)\right) \le \operatorname{opnorm}\left(A - \operatorname{mu2}\left(A, B, s\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.claim` (`✓ std3`).

*Citation.* Raluca Dumitru; Jose Franco (2017). *On the monotonicity of weighted power means of matrices*. URL: <https://arxiv.org/abs/1701.07023v1>.

*Commentary.*

The closed proposition quantifies over every finite dimension n, positive semidefinite complex matrices A,B, and real s,t with 0≤s≤t≤1. It requires ‖A−mu2 A B t‖≤‖A−mu2 A B s‖. The direction is nonincreasing in t. Every matrix norm in this statement is Matrix.Norms.L2Operator, the norm induced by EuclideanSpace C (Fin n). The full v1 all-norm assertion implies this specialization; claim does not encode that full assertion.

**Definition 1.3 (The matrix B).**

Lean statement: `D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.X`

*Formalization.* `D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.X` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Raluca Dumitru; Jose Franco (2017). *On the monotonicity of weighted power means of matrices*. URL: <https://arxiv.org/abs/1701.07023v1>.

*Commentary.*

X=diag(1/10,4). Its first leading principal minor is 1/10 and its determinant is 2/5, so it is positive definite over C.

**Definition 1.4 (The matrix A).**

Lean statement: `D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.Y`

*Formalization.* `D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.Y` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Raluca Dumitru; Jose Franco (2017). *On the monotonicity of weighted power means of matrices*. URL: <https://arxiv.org/abs/1701.07023v1>.

*Commentary.*

Y=[[19/50,−24/25],[−24/25,93/25]]. Its first leading principal minor is 19/50 and its determinant is 123/250, so it is positive definite over C.

For A=Y and B=X, the endpoint distance at s=0 is exactly 1, and the distance at t=1/100 is strictly greater than 1. Indeed, D=X−Y satisfies D*D=I. At t=1/100 the weighted square is S=[[257/12500,−123/3125],[−123/3125,39969/2500]]. Put d=51118101/156250000, T=100051/6250, r=√d and w=√(T+2r). Positivity and (S+rI)²=(T+2r)S identify its positive spectral root as Q=(S+rI)/w. For the Euclidean unit vector v=(3/5,4/5), v*Sv=127521/12500, v*Xv=649/250 and v*Yv=399/250. The exact inequality r>57/100 gives (v*Sv+r)/w>649/250, hence v*(Q−Y)v>1. Cauchy–Schwarz and the Euclidean induced operator-norm bound give ‖Q−Y‖>1. The endpoint uses the positive spectral root of X², namely X. An entry maximum, infinity-induced norm, or Frobenius norm is never substituted.

**Theorem 1.5 (The specialized proposition is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Raluca Dumitru; Jose Franco (2017). *On the monotonicity of weighted power means of matrices*. URL: <https://arxiv.org/abs/1701.07023v1>.

*Commentary.*

The theorem is literally Not claim, with no additional assumptions. The witnesses n=2, A=Y, B=X, s=0, t=1/100 meet the PSD and ordered-parameter hypotheses and contradict the required nonincreasing distance. This single Euclidean operator norm is unitarily invariant, so the counterexample also contradicts the v1 universal all-norm assertion by specialization. It does not refute every norm separately or the known p=2 Frobenius statement.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.X`
- Truth anchor: `D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.Y`
- Truth anchor: `D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.mu2`
- Truth anchor: `D5/S3/Quantum/Matrix/PowerMeanOperatorRefutation.result`
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](SpectralPower.md)
