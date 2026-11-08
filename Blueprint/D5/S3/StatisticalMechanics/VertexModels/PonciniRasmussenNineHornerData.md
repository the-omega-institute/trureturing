# Integer data for nine strands

## Abstract

Integer data for nine strands

The 4862 diagram coordinates are padded to 8192. Binary tree lookup takes the left subtree for an even index and the right subtree for an odd index, then divides the index by two. The incoming rows retain multiplicity. The private vectors v0 through v58 are literal integer trees. Their recurrence and endpoint values are separate checked theorems.

**Definition 1.1 (annihilatorCoefficients).**

$$annihilatorCoefficients = \operatorname{List}\left(1, 0, \operatorname{Negate}\left(163\right), 0, 12285, 0, \operatorname{Negate}\left(569445\right), 0, 18215115, 0, \operatorname{Negate}\left(427662891\right), 0, 7652877936, 0, \operatorname{Negate}\left(106986874650\right), 0, 1188246329388, 0, \operatorname{Negate}\left(10605723426434\right), 0, 76659122475479, 0, \operatorname{Negate}\left(450854928573687\right), 0, 2162620108980042, 0, \operatorname{Negate}\left(8462844884056308\right), 0, 26973986982247197, 0, \operatorname{Negate}\left(69786597194594871\right), 0, 145778728152448221, 0, \operatorname{Negate}\left(244086630072528699\right), 0, 324477075047489821, 0, \operatorname{Negate}\left(338328989148555271\right), 0, 272486148975235188, 0, \operatorname{Negate}\left(166252500600659604\right), 0, 74962166731413102, 0, \operatorname{Negate}\left(24185673946500264\right), 0, 5347591521504921, 0, \operatorname{Negate}\left(762922848588417\right), 0, 64282035899880, 0, \operatorname{Negate}\left(2771640702288\right), 0, 43808164416, 0\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.annihilatorCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The list is in highest-degree-first order.

**Definition 1.2 (sparseHamiltonian).**

$$\forall v \in \operatorname{Function}\left(\operatorname{Fin}\left(8192\right), Int\right),\; \forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{sparseHamiltonian}\left(v, i\right) = \operatorname{Negate}\left(\operatorname{FoldLeft}\left(\operatorname{get}\left(rows, \operatorname{val}\left(i\right)\right), \operatorname{AddIncomingCoefficient}\left(v, 8192\right), 0\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.sparseHamiltonian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

AddIncomingCoefficient(s,j) is s+v(j modulo 8192).

**Definition 1.3 (hornerValue).**

$$hornerValue = \operatorname{FoldLeft}\left(annihilatorCoefficients, HornerStep, ZeroVector\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.hornerValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

HornerStep(v,c)(i) equals sparseHamiltonian(v)(i) plus c at coordinate 4861 and zero elsewhere. The initial vector is zero.

**Definition 1.4 (state).**

$$\forall k \in Nat,\; \forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{state}\left(k, i\right) = \operatorname{get}\left(\operatorname{MatchNat}\left(k, \operatorname{Branch}\left(0, v0\right), \operatorname{Branch}\left(1, v1\right), \operatorname{Branch}\left(2, v2\right), \operatorname{Branch}\left(3, v3\right), \operatorname{Branch}\left(4, v4\right), \operatorname{Branch}\left(5, v5\right), \operatorname{Branch}\left(6, v6\right), \operatorname{Branch}\left(7, v7\right), \operatorname{Branch}\left(8, v8\right), \operatorname{Branch}\left(9, v9\right), \operatorname{Branch}\left(10, v10\right), \operatorname{Branch}\left(11, v11\right), \operatorname{Branch}\left(12, v12\right), \operatorname{Branch}\left(13, v13\right), \operatorname{Branch}\left(14, v14\right), \operatorname{Branch}\left(15, v15\right), \operatorname{Branch}\left(16, v16\right), \operatorname{Branch}\left(17, v17\right), \operatorname{Branch}\left(18, v18\right), \operatorname{Branch}\left(19, v19\right), \operatorname{Branch}\left(20, v20\right), \operatorname{Branch}\left(21, v21\right), \operatorname{Branch}\left(22, v22\right), \operatorname{Branch}\left(23, v23\right), \operatorname{Branch}\left(24, v24\right), \operatorname{Branch}\left(25, v25\right), \operatorname{Branch}\left(26, v26\right), \operatorname{Branch}\left(27, v27\right), \operatorname{Branch}\left(28, v28\right), \operatorname{Branch}\left(29, v29\right), \operatorname{Branch}\left(30, v30\right), \operatorname{Branch}\left(31, v31\right), \operatorname{Branch}\left(32, v32\right), \operatorname{Branch}\left(33, v33\right), \operatorname{Branch}\left(34, v34\right), \operatorname{Branch}\left(35, v35\right), \operatorname{Branch}\left(36, v36\right), \operatorname{Branch}\left(37, v37\right), \operatorname{Branch}\left(38, v38\right), \operatorname{Branch}\left(39, v39\right), \operatorname{Branch}\left(40, v40\right), \operatorname{Branch}\left(41, v41\right), \operatorname{Branch}\left(42, v42\right), \operatorname{Branch}\left(43, v43\right), \operatorname{Branch}\left(44, v44\right), \operatorname{Branch}\left(45, v45\right), \operatorname{Branch}\left(46, v46\right), \operatorname{Branch}\left(47, v47\right), \operatorname{Branch}\left(48, v48\right), \operatorname{Branch}\left(49, v49\right), \operatorname{Branch}\left(50, v50\right), \operatorname{Branch}\left(51, v51\right), \operatorname{Branch}\left(52, v52\right), \operatorname{Branch}\left(53, v53\right), \operatorname{Branch}\left(54, v54\right), \operatorname{Branch}\left(55, v55\right), \operatorname{Branch}\left(56, v56\right), \operatorname{Branch}\left(57, v57\right), \operatorname{Default}\left(v58\right)\right), \operatorname{val}\left(i\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.state` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All states, including the default v58, are literal integer vectors.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.annihilatorCoefficients`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.hornerValue`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.sparseHamiltonian`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData.state`
