# The open quantum walk hitting-time formula is false

## Abstract

A complex reset pair refutes the proposed three-entry formula for gambler's-ruin mean hitting times.

**Definition 1.1 (The time-ordered branch operator).**

$$\forall (l: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (r: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (w: \operatorname{List}\left(\operatorname{Bool}\right)), (\operatorname{D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation.wordOperator}\left(l, r, w\right) = \operatorname{List.prod}\left(\operatorname{List.reverse}\left(\operatorname{List.map}\left((\lambda (b: \operatorname{Bool}) \mapsto (\operatorname{ite}\left(b = \operatorname{Bool.true}, r, l\right))), w\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.wordOperator` (`✓ std3`).

*Citation.* Thomas S. Jacq; Carlos F. Lardizabal (2017). *Open Quantum Random Walks on the Half-Line: The Karlin–McGregor Formula, Path Counting and Foster's Theorem*. DOI: [10.1007/s10955-017-1876-x](https://doi.org/10.1007/s10955-017-1876-x). URL: <https://arxiv.org/abs/1701.08400v3>.

*Commentary.*

For a word of Boolean steps, false selects the left matrix l and true selects the right matrix r. The mapped word is reversed before multiplying, so the last step is the leftmost factor. This is the ordered branch product used in the stopped-path expansion of the open quantum walk (JL_rev2.tex, lines 77–83 and 120–121).

**Definition 1.2 (The integer position after a prefix).**

$$\forall (k: \mathbb{N}), (\forall (w: \operatorname{List}\left(\operatorname{Bool}\right)), (\forall (t: \mathbb{N}), (\operatorname{D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation.position}\left(k, w, t\right) = ((\operatorname{Nat.cast}\left(k\right): \mathbb{Z})) + (\operatorname{List.sum}\left(\operatorname{List.map}\left((\lambda (b: \operatorname{Bool}) \mapsto (\operatorname{ite}\left(b = \operatorname{Bool.true}, (1: \mathbb{Z}), -((1: \mathbb{Z}))\right))), \operatorname{List.take}\left(t, w\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.position` (`✓ std3`).

*Citation.* Thomas S. Jacq; Carlos F. Lardizabal (2017). *Open Quantum Random Walks on the Half-Line: The Karlin–McGregor Formula, Path Counting and Foster's Theorem*. DOI: [10.1007/s10955-017-1876-x](https://doi.org/10.1007/s10955-017-1876-x). URL: <https://arxiv.org/abs/1701.08400v3>.

*Commentary.*

Starting at the natural position k, add one for each true step and subtract one for each false step in the first t letters. The integer codomain records leftward motion without truncation. This is the lattice-path position underlying the gambler's-ruin walk (JL_rev2.tex, lines 300–301).

**Definition 1.3 (First absorption at a boundary).**

$$\forall (m: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (w: \operatorname{List}\left(\operatorname{Bool}\right)), (\operatorname{D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation.firstAbsorbs}\left(m, k, w\right) = \left((\forall (t: \mathbb{N}), ((t < \operatorname{List.length}\left(w\right)) \Rightarrow (((0: \mathbb{Z}) < \operatorname{D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation.position}\left(k, w, t\right)) \land (\operatorname{D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation.position}\left(k, w, t\right) < (\operatorname{Nat.cast}\left(m\right): \mathbb{Z}))))) \land ((\operatorname{D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation.position}\left(k, w, \operatorname{List.length}\left(w\right)\right) = (0: \mathbb{Z})) \lor (\operatorname{D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation.position}\left(k, w, \operatorname{List.length}\left(w\right)\right) = (\operatorname{Nat.cast}\left(m\right): \mathbb{Z})))\right))))$$

*Formalization.* `D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.firstAbsorbs` (`✓ std3`).

*Citation.* Thomas S. Jacq; Carlos F. Lardizabal (2017). *Open Quantum Random Walks on the Half-Line: The Karlin–McGregor Formula, Path Counting and Foster's Theorem*. DOI: [10.1007/s10955-017-1876-x](https://doi.org/10.1007/s10955-017-1876-x). URL: <https://arxiv.org/abs/1701.08400v3>.

*Commentary.*

A word first absorbs the walk from k in the interval with boundaries 0 and m when every strict prefix remains strictly between the boundaries and the full word ends at one of them. The prefix condition is the monitoring convention for reaching a boundary for the first time (JL_rev2.tex, lines 1081–1083).

**Definition 1.4 (The mass absorbed at a fixed time).**

$$\forall (l: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (r: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (m: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (n: \mathbb{N}), (\operatorname{D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation.absorbedMass}\left(l, r, m, k, \rho, n\right) = \operatorname{List.sum}\left(\operatorname{List.map}\left((\lambda (w: \operatorname{List}\left(\operatorname{Bool}\right)) \mapsto (\operatorname{ite}\left(\operatorname{D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation.firstAbsorbs}\left(m, k, w\right), \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(((\operatorname{D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation.wordOperator}\left(l, r, w\right)) \cdot (\rho)) \cdot (\operatorname{Matrix.conjTranspose}\left(\operatorname{D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation.wordOperator}\left(l, r, w\right)\right))\right)\right), (0: \mathbb{R})\right))), \operatorname{List.sections}\left(\operatorname{List.replicate}\left(n, [\operatorname{Bool.false}, \operatorname{Bool.true}]\right)\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.absorbedMass` (`✓ std3`).

*Citation.* Thomas S. Jacq; Carlos F. Lardizabal (2017). *Open Quantum Random Walks on the Half-Line: The Karlin–McGregor Formula, Path Counting and Foster's Theorem*. DOI: [10.1007/s10955-017-1876-x](https://doi.org/10.1007/s10955-017-1876-x). URL: <https://arxiv.org/abs/1701.08400v3>.

*Commentary.*

Generate all Boolean words of length n by taking sections of n copies of the two-letter block [false,true]. For each word first absorbed at time n, take the real part of the trace of its unnormalized branch matrix W ρ Wᴴ; all other words contribute zero. Summing these terms gives the stopped-path mass used in the source's first-visit probabilities (JL_rev2.tex, lines 1081–1086).

**Definition 1.5 (The extended mean first absorption time).**

$$\forall (l: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (r: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (m: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation.meanHittingTime}\left(l, r, m, k, \rho\right) = \operatorname{tsum}\left((\lambda (n: \mathbb{N}) \mapsto (((\operatorname{Nat.cast}\left(n\right): ENNReal)) \cdot (\operatorname{ENNReal.ofReal}\left(\operatorname{D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation.absorbedMass}\left(l, r, m, k, \rho, n\right)\right))))\right))))))$$

*Formalization.* `D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.meanHittingTime` (`✓ std3`).

*Citation.* Thomas S. Jacq; Carlos F. Lardizabal (2017). *Open Quantum Random Walks on the Half-Line: The Karlin–McGregor Formula, Path Counting and Foster's Theorem*. DOI: [10.1007/s10955-017-1876-x](https://doi.org/10.1007/s10955-017-1876-x). URL: <https://arxiv.org/abs/1701.08400v3>.

*Commentary.*

Weight the absorbed mass at each natural time n by n, regard the weight as an extended nonnegative real, and sum over all times. The value may be infinite, matching the source's expected time to reach either boundary (JL_rev2.tex, lines 1087–1091).

**Definition 1.6 (The proposed dependence on three real matrix entries).**

$$\forall (l: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\forall (r: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), ((((\operatorname{Matrix.conjTranspose}\left(l\right)) \cdot (l)) + ((\operatorname{Matrix.conjTranspose}\left(r\right)) \cdot (r)) = (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))) \Rightarrow (\forall (m: \mathbb{N}), (((3: \mathbb{N}) \le m) \Rightarrow (\exists (h: \mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right)), (\exists (j: \mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right)), ((\forall (k: \mathbb{N}), (((1: \mathbb{N}) \le k) \Rightarrow ((k \le (m) - (1)) \Rightarrow (j\left(m\right)\left(k\right) = -(j\left(m\right)\left((m) - (k)\right)))))) \land (\forall (k: \mathbb{N}), (((1: \mathbb{N}) \le k) \Rightarrow ((k \le (m) - (1)) \Rightarrow (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)) \Rightarrow ((\operatorname{D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation.meanHittingTime}\left(l, r, m, k, \rho\right) \ne \operatorname{top}) \land (\operatorname{ENNReal.toReal}\left(\operatorname{D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation.meanHittingTime}\left(l, r, m, k, \rho\right)\right) = ((((1: \mathbb{R})) + ((h\left(m\right)\left((m) - (k)\right)) \cdot (\operatorname{Complex.re}\left(\rho\left(0\right)\left(0\right)\right)))) + ((h\left(m\right)\left(k\right)) \cdot (\operatorname{Complex.re}\left(\rho\left(1\right)\left(1\right)\right)))) + ((j\left(m\right)\left(k\right)) \cdot (\operatorname{Complex.re}\left(\rho\left(0\right)\left(1\right)\right)))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Thomas S. Jacq; Carlos F. Lardizabal (2017). *Open Quantum Random Walks on the Half-Line: The Karlin–McGregor Formula, Path Counting and Foster's Theorem*. DOI: [10.1007/s10955-017-1876-x](https://doi.org/10.1007/s10955-017-1876-x). URL: <https://arxiv.org/abs/1701.08400v3>.

*Commentary.*

For every pair of two-dimensional complex transition matrices satisfying lᴴl + rᴴr = 1 and every m at least 3, the claim supplies two real functions h and j of the two natural indices. The function j is antisymmetric under k ↦ m − k. For every interior starting position and every density matrix, the meanHittingTime is finite and its real value is the affine expression using the two diagonal real entries and the real part of the upper-right entry. This is the formal reading of Remark 5.3 (JL_rev2.tex, lines 1291–1293).

**Theorem 1.7 (A complex reset pair refutes the claim).**

$$\neg (\operatorname{D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/jacq-lardizabal-2017-oqw-gambler-mean-hitting-time-form` (refuted) by `D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"jacq-lardizabal-2017-oqw-gambler-mean-hitting-time-form","declaration_gid":"D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Thomas S. Jacq; Carlos F. Lardizabal (2017). *Open Quantum Random Walks on the Half-Line: The Karlin–McGregor Formula, Path Counting and Foster's Theorem*. DOI: [10.1007/s10955-017-1876-x](https://doi.org/10.1007/s10955-017-1876-x). URL: <https://arxiv.org/abs/1701.08400v3>.

*Commentary.*

Let u = (1, i) and v = (1, −i), indexed by Fin 2, and set l = (1/2) v uᴴ, r = (1/2) v vᴴ, ρ = (1/2) u uᴴ, and σ = (1/2) v vᴴ. Exact entrywise calculation gives lᴴl + rᴴr = 1 and l r = 0. The matrices ρ and σ are positive semidefinite with trace one, so both satisfy IsDensity.

The stopped-word calculation uses l r = 0: every first-absorbing word of length at least three contains the consecutive subword [true,false], whose branch operator is l r, so all absorbed masses after time two vanish. At time one only [false] absorbs and contributes trace(l ρ lᴴ); at time two only [true,true] absorbs and contributes trace((r r) ρ (r r)ᴴ). Thus meanHittingTime is the sum of the time-one mass and twice the time-two mass.

Substituting the four explicit matrices into that two-step formula gives meanHittingTime l r 3 1 ρ = 1 and meanHittingTime l r 3 1 σ = 2. The three entries used by the claimed affine expression agree for ρ and σ: both diagonal real entries are one half and the real part of the upper-right entry is zero.

If the claim held, instantiate it with l, r, m = 3, and k = 1. The common three entries would force the two real mean values to be equal, while the explicit computation makes them 1 and 2. This contradiction proves ¬ claim.

## References

- Truth anchor: `D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.absorbedMass`
- Truth anchor: `D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.firstAbsorbs`
- Truth anchor: `D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.meanHittingTime`
- Truth anchor: `D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.position`
- Truth anchor: `D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.result`
- Truth anchor: `D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.wordOperator`
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](../Information/SLDSpectralEnergy.md)
