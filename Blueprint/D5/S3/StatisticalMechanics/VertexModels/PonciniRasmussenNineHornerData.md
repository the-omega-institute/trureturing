# Integer data for nine strands

## Abstract

Integer data for nine strands

The 4862 diagram coordinates are embedded in Fin 8192. The shared D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree.get function reads the common Tree by parity and division by two. D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner.rows is the single incoming row table, also used by D5.S3.StatisticalMechanics.PonciniRasmussenNineEdges.incoming. The private v0 through v58 are the integer state trees.

**Definition 1.1 (rows).**

$$(\operatorname{rows}: \operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{PonciniRasmussenCertificateTree}.\operatorname{Tree}\left(\operatorname{List}\left(\operatorname{Nat}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.rows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal tree contains 8192 incoming source lists. For i : Fin 8192, D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree.get D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner.rows i.val selects the list at i. Its natural source indices retain their multiplicities; sparseHamiltonian reduces them modulo 8192 with Nat.mod_lt.

**Definition 1.2 (annihilatorCoefficients).**

$$\operatorname{annihilatorCoefficients} = [1, 0, -(163), 0, 12285, 0, -(569445), 0, 18215115, 0, -(427662891), 0, 7652877936, 0, -(106986874650), 0, 1188246329388, 0, -(10605723426434), 0, 76659122475479, 0, -(450854928573687), 0, 2162620108980042, 0, -(8462844884056308), 0, 26973986982247197, 0, -(69786597194594871), 0, 145778728152448221, 0, -(244086630072528699), 0, 324477075047489821, 0, -(338328989148555271), 0, 272486148975235188, 0, -(166252500600659604), 0, 74962166731413102, 0, -(24185673946500264), 0, 5347591521504921, 0, -(762922848588417), 0, 64282035899880, 0, -(2771640702288), 0, 43808164416, 0]$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.annihilatorCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These 58 integers are in highest-degree-first order.

**Definition 1.3 (sparseHamiltonian).**

$$\forall (v: (\operatorname{Fin}\left(8192\right)) \to (\operatorname{Int})), (\operatorname{sparseHamiltonian}\left(v\right) = ((i: \operatorname{Fin}\left(8192\right)) \mapsto -(\operatorname{List}.\operatorname{foldl}\left(((s: \operatorname{Int}) \mapsto ((j: \operatorname{Nat}) \mapsto (s) + (v\left(\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Nat}.\operatorname{mod}\left(j, 8192\right), \operatorname{Nat}.\operatorname{mod_{lt}}\left(j, \operatorname{by} \operatorname{omega}\right)\right)\right)))), 0, \operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{PonciniRasmussenCertificateTree}.\operatorname{get}\left(\operatorname{rows}, \operatorname{Fin}.\operatorname{val}\left(i\right)\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.sparseHamiltonian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum retains repeated source coordinates and uses the negative Hamiltonian sign.

**Definition 1.4 (hornerValue).**

$$\operatorname{hornerValue} = \operatorname{List}.\operatorname{foldl}\left(((v: (\operatorname{Fin}\left(8192\right)) \to (\operatorname{Int})) \mapsto ((c: \operatorname{Int}) \mapsto ((i: \operatorname{Fin}\left(8192\right)) \mapsto (\operatorname{sparseHamiltonian}\left(v, i\right)) + (\operatorname{ite}\left(\operatorname{BEq}.\operatorname{beq}\left(\operatorname{Fin}.\operatorname{val}\left(i\right), 4861\right), c, 0\right))))), \operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(8192\right), 0\right), \operatorname{annihilatorCoefficients}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.hornerValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The callback adds c only at the identity coordinate. Its initial function is constant zero.

**Definition 1.5 (state).**

$$\forall (k: \operatorname{Nat}), (\operatorname{state}\left(k\right) = ((i: \operatorname{Fin}\left(8192\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{PonciniRasmussenCertificateTree}.\operatorname{get}\left((\operatorname{match} k \operatorname{with} | 0 \mapsto \operatorname{v0} | 1 \mapsto \operatorname{v1} | 2 \mapsto \operatorname{v2} | 3 \mapsto \operatorname{v3} | 4 \mapsto \operatorname{v4} | 5 \mapsto \operatorname{v5} | 6 \mapsto \operatorname{v6} | 7 \mapsto \operatorname{v7} | 8 \mapsto \operatorname{v8} | 9 \mapsto \operatorname{v9} | 10 \mapsto \operatorname{v10} | 11 \mapsto \operatorname{v11} | 12 \mapsto \operatorname{v12} | 13 \mapsto \operatorname{v13} | 14 \mapsto \operatorname{v14} | 15 \mapsto \operatorname{v15} | 16 \mapsto \operatorname{v16} | 17 \mapsto \operatorname{v17} | 18 \mapsto \operatorname{v18} | 19 \mapsto \operatorname{v19} | 20 \mapsto \operatorname{v20} | 21 \mapsto \operatorname{v21} | 22 \mapsto \operatorname{v22} | 23 \mapsto \operatorname{v23} | 24 \mapsto \operatorname{v24} | 25 \mapsto \operatorname{v25} | 26 \mapsto \operatorname{v26} | 27 \mapsto \operatorname{v27} | 28 \mapsto \operatorname{v28} | 29 \mapsto \operatorname{v29} | 30 \mapsto \operatorname{v30} | 31 \mapsto \operatorname{v31} | 32 \mapsto \operatorname{v32} | 33 \mapsto \operatorname{v33} | 34 \mapsto \operatorname{v34} | 35 \mapsto \operatorname{v35} | 36 \mapsto \operatorname{v36} | 37 \mapsto \operatorname{v37} | 38 \mapsto \operatorname{v38} | 39 \mapsto \operatorname{v39} | 40 \mapsto \operatorname{v40} | 41 \mapsto \operatorname{v41} | 42 \mapsto \operatorname{v42} | 43 \mapsto \operatorname{v43} | 44 \mapsto \operatorname{v44} | 45 \mapsto \operatorname{v45} | 46 \mapsto \operatorname{v46} | 47 \mapsto \operatorname{v47} | 48 \mapsto \operatorname{v48} | 49 \mapsto \operatorname{v49} | 50 \mapsto \operatorname{v50} | 51 \mapsto \operatorname{v51} | 52 \mapsto \operatorname{v52} | 53 \mapsto \operatorname{v53} | 54 \mapsto \operatorname{v54} | 55 \mapsto \operatorname{v55} | 56 \mapsto \operatorname{v56} | 57 \mapsto \operatorname{v57} | _ \mapsto \operatorname{v58}), \operatorname{Fin}.\operatorname{val}\left(i\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.state` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The match has branches 0 through 57; every other natural number selects v58.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.annihilatorCoefficients`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.hornerValue`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.rows`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.sparseHamiltonian`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.state`
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenCertificateTree](PonciniRasmussenCertificateTree.md)
