# Five-row one-defect strips

## Abstract

Five-row HA arrays with exactly one equal-colour bond.

Bonds join (i,j) to (i,j+1) and (i,j+1) to (i+1,j), within the array. The column sweep preserves these bonds; the canonical predicate always reads cells in row-major order. Exactly one bond has equal endpoint colours.

**Definition 1.1 (a).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229590}.\operatorname{HardinA229590Strip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: \operatorname{Prod}\left(\operatorname{Fin}\left(5\right), \operatorname{Fin}\left(n\right)\right) \to \operatorname{Fin}\left(3\right)) \mapsto (\operatorname{DefectTransfer}.\operatorname{defects}\left((\operatorname{Finset}.\operatorname{empty}\left(\right): \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(5\right), \operatorname{Fin}\left(5\right)\right)\right)), \operatorname{HardinA229590StripData}.\operatorname{between}\left(\right), \operatorname{List}.\operatorname{ofFn}\left((\lambda (j: \operatorname{Fin}\left(n\right)) \mapsto (\lambda (i: \operatorname{Fin}\left(5\right)) \mapsto A\left((i, j)\right)))\right)\right) = 1) \land (\forall (p: \operatorname{Prod}\left(\operatorname{Fin}\left(5\right), \operatorname{Fin}\left(n\right)\right)), (\forall (c: \operatorname{Fin}\left(3\right)), ((c < A\left(p\right)) \Rightarrow (\exists (q: \operatorname{Prod}\left(\operatorname{Fin}\left(5\right), \operatorname{Fin}\left(n\right)\right)), (((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right) < (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right)) \land (A\left(q\right) = c))))))), \operatorname{Finset}.\operatorname{univ}\left(\right)\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229590: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229590>.

*Commentary.*

All arrays are filtered by exactly one equal-colour bond and literal row-major colour introduction. The rank of (i,j) is i*n+j.

**Theorem 1.2 (finite certificate).**

$$(\forall (p: \operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), (\forall (d: \operatorname{Fin}\left(2\right)), (\forall (s: \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Fin}\left(41\right)\right)), (\sum_{r: \operatorname{Fin}\left(5\right) \to \operatorname{Fin}\left(3\right)} ((\operatorname{if} ((\operatorname{HardinA229590StripData}.\operatorname{cross}\left(p, r\right) \le \operatorname{Fin}.\operatorname{val}\left(d\right)) \land (\operatorname{HardinA229590StripData}.\operatorname{cl}\left(\operatorname{HardinA229590StripData}.\operatorname{boundary}\left(r\right), (\operatorname{Fin}.\operatorname{val}\left(d\right)) - (\operatorname{HardinA229590StripData}.\operatorname{cross}\left(p, r\right))\right) = s)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{HardinA229590StripData}.\operatorname{T}\left(\operatorname{HardinA229590StripData}.\operatorname{cl}\left(p, \operatorname{Fin}.\operatorname{val}\left(d\right)\right), s\right))))) \land ((\forall (s: \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Fin}\left(41\right)\right)), (\sum_{r: \operatorname{Fin}\left(5\right) \to \operatorname{Fin}\left(3\right)} ((\operatorname{if} (\operatorname{HardinA229590StripData}.\operatorname{cl}\left(\operatorname{HardinA229590StripData}.\operatorname{boundary}\left(r\right), 1\right) = s) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{HardinA229590StripData}.\operatorname{initial}\left(s\right))) \land (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229590StripData}.\operatorname{T}\left(\right)^{4 + 14}, \operatorname{HardinA229590StripData}.\operatorname{terminal}\left(\right)\right) = \sum_{j: \operatorname{Fin}\left(14\right)} (\operatorname{HSMul}.\operatorname{hSMul}\left(\begin{pmatrix}(-64)&768&(-3648)&8336&(-7472)&(-5464)&18879&(-14888)&(-816)&9016&(-6494)&2200&(-384)&32\end{pmatrix}\left(j\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229590StripData}.\operatorname{T}\left(\right)^{4 + \operatorname{Fin}.\operatorname{val}\left(j\right)}, \operatorname{HardinA229590StripData}.\operatorname{terminal}\left(\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229590: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229590>.

*Commentary.*

The transfer sums, initial multiplicities and terminal-vector polynomial give an exact finite counting identity.

**Theorem 1.3 (result).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229590}.\operatorname{HardinA229590Strip}.\operatorname{a}\left(n + 19\right): \operatorname{Int}) = (((((((((32) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229590}.\operatorname{HardinA229590Strip}.\operatorname{a}\left(n + 18\right): \operatorname{Int}))) - ((384) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229590}.\operatorname{HardinA229590Strip}.\operatorname{a}\left(n + 17\right): \operatorname{Int}))) + (2200) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229590}.\operatorname{HardinA229590Strip}.\operatorname{a}\left(n + 16\right): \operatorname{Int}))) - ((6494) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229590}.\operatorname{HardinA229590Strip}.\operatorname{a}\left(n + 15\right): \operatorname{Int}))) + (9016) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229590}.\operatorname{HardinA229590Strip}.\operatorname{a}\left(n + 14\right): \operatorname{Int}))) - ((816) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229590}.\operatorname{HardinA229590Strip}.\operatorname{a}\left(n + 13\right): \operatorname{Int})))) - ((14888) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229590}.\operatorname{HardinA229590Strip}.\operatorname{a}\left(n + 12\right): \operatorname{Int}))) + (18879) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229590}.\operatorname{HardinA229590Strip}.\operatorname{a}\left(n + 11\right): \operatorname{Int}))) - ((5464) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229590}.\operatorname{HardinA229590Strip}.\operatorname{a}\left(n + 10\right): \operatorname{Int})))) - ((7472) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229590}.\operatorname{HardinA229590Strip}.\operatorname{a}\left(n + 9\right): \operatorname{Int}))) + (8336) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229590}.\operatorname{HardinA229590Strip}.\operatorname{a}\left(n + 8\right): \operatorname{Int}))) - ((3648) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229590}.\operatorname{HardinA229590Strip}.\operatorname{a}\left(n + 7\right): \operatorname{Int}))) + (768) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229590}.\operatorname{HardinA229590Strip}.\operatorname{a}\left(n + 6\right): \operatorname{Int}))) - ((64) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229590}.\operatorname{HardinA229590Strip}.\operatorname{a}\left(n + 5\right): \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229590` (proved) by `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229590","declaration_gid":"D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229590: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229590>.

*Commentary.*

For every natural n, the literal count at n+19 satisfies the stated fourteen-lag recurrence. Coordinate exchange counts the same labelled arrays. Colour relabelling gives six labelled arrays for each canonical representative.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripCut](HardinA229590StripCut.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripData](HardinA229590StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripPowers](HardinA229590StripPowers.md)
