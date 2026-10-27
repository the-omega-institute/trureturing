# Elementary channel divisibility

## Abstract

Exact Kraus-space criterion for elementary right division of finite quantum channels.

The index type I is finite. Matrices act on the complex coordinate space I → ℂ. The inner product is conjugate linear in its first argument, and tr denotes Matrix.trace. CP is the existing complete-positivity predicate, quantifying every finite amplification; CPTP also preserves the trace of every matrix. No assertion about a physical gate set, a local operations protocol, a success probability or a preparation cost follows from these statements.

**Definition 1.1 (Ordered orthogonal unit pair).**

$$\forall (\operatorname{I}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{I}))][(\operatorname{DecidableEq}(\operatorname{I}))], \forall (\operatorname{x}:(\operatorname{I}\to\mathbb{C})), \forall (\operatorname{y}:(\operatorname{I}\to\mathbb{C})), (((\operatorname{OrthogonalUnitPair}(\operatorname{x},\operatorname{y})))\Leftrightarrow(((\langle\operatorname{x},\operatorname{x}\rangle=1)\land(\langle\operatorname{y},\operatorname{y}\rangle=1)\land(\langle\operatorname{x},\operatorname{y}\rangle=0))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.OrthogonalUnitPair` (`✓ std3`).

*Citation.* Frederik vom Ende (2024). *A Sufficient Criterion for Divisibility of Quantum Channels*. DOI: [10.1063/5.0231812](https://doi.org/10.1063/5.0231812). URL: <https://arxiv.org/html/2407.17103v3>.

*Commentary.*

The two vectors are separately normalized and orthogonal in the displayed order.

**Definition 1.2 (Rank one operator).**

$$\forall (\operatorname{I}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{I}))][(\operatorname{DecidableEq}(\operatorname{I}))], \forall (\operatorname{u}:(\operatorname{I}\to\mathbb{C})), \forall (\operatorname{v}:(\operatorname{I}\to\mathbb{C})), (\operatorname{ketbra}(\operatorname{u},\operatorname{v}))=(\operatorname{vecMulVec}(\operatorname{u},(\operatorname{star}(\operatorname{v}))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.ketbra` (`✓ std3`).

*Citation.* Frederik vom Ende (2024). *A Sufficient Criterion for Divisibility of Quantum Channels*. DOI: [10.1063/5.0231812](https://doi.org/10.1063/5.0231812). URL: <https://arxiv.org/html/2407.17103v3>.

*Commentary.*

The operator ketbra(u,v) sends z to u⟨v,z⟩.

**Theorem 1.3 (Adjoint of a rank one operator).**

$$\forall (\operatorname{n}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{n}))][(\operatorname{DecidableEq}(\operatorname{n}))], \forall (\operatorname{u}:(\operatorname{n}\to\mathbb{C})), \forall (\operatorname{w}:(\operatorname{n}\to\mathbb{C})), ((\operatorname{ketbra}(\operatorname{u},\operatorname{w})))^{*}=(\operatorname{ketbra}(\operatorname{w},\operatorname{u}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.ketbra_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2024). *A Sufficient Criterion for Divisibility of Quantum Channels*. DOI: [10.1063/5.0231812](https://doi.org/10.1063/5.0231812). URL: <https://arxiv.org/html/2407.17103v3>.

*Commentary.*

Taking the adjoint exchanges the two vectors of the rank one operator.

**Definition 1.4 (First elementary Kraus operator).**

$$\forall (\operatorname{I}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{I}))][(\operatorname{DecidableEq}(\operatorname{I}))], \forall (\operatorname{t}:\mathbb{R}), \forall (\operatorname{x}:(\operatorname{I}\to\mathbb{C})), (\operatorname{elementaryK}(\operatorname{t},\operatorname{x}))=(1+(((\sqrt{(1-\operatorname{t})}-1))\cdot((\operatorname{ketbra}(\operatorname{x},\operatorname{x})))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.elementaryK` (`✓ std3`).

*Citation.* Frederik vom Ende (2024). *A Sufficient Criterion for Divisibility of Quantum Channels*. DOI: [10.1063/5.0231812](https://doi.org/10.1063/5.0231812). URL: <https://arxiv.org/html/2407.17103v3>.

*Commentary.*

This is Kₜ = I − (1 − √(1−t))|x⟩⟨x| from Definition 1. The real square root is embedded in ℂ.

**Definition 1.5 (Second elementary Kraus operator).**

$$\forall (\operatorname{I}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{I}))][(\operatorname{DecidableEq}(\operatorname{I}))], \forall (\operatorname{t}:\mathbb{R}), \forall (\operatorname{x}:(\operatorname{I}\to\mathbb{C})), \forall (\operatorname{y}:(\operatorname{I}\to\mathbb{C})), (\operatorname{elementaryL}(\operatorname{t},\operatorname{x},\operatorname{y}))=((\sqrt{\operatorname{t}})\cdot((\operatorname{ketbra}(\operatorname{y},\operatorname{x}))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.elementaryL` (`✓ std3`).

*Citation.* Frederik vom Ende (2024). *A Sufficient Criterion for Divisibility of Quantum Channels*. DOI: [10.1063/5.0231812](https://doi.org/10.1063/5.0231812). URL: <https://arxiv.org/html/2407.17103v3>.

*Commentary.*

This is Lₜ = √t |y⟩⟨x| from Definition 1, with the real coefficient embedded in ℂ.

**Definition 1.6 (Elementary channel).**

$$\forall (\operatorname{I}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{I}))][(\operatorname{DecidableEq}(\operatorname{I}))], \forall (\operatorname{t}:\mathbb{R}), \forall (\operatorname{x}:(\operatorname{I}\to\mathbb{C})), \forall (\operatorname{y}:(\operatorname{I}\to\mathbb{C})), \forall (\operatorname{X}:(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))), ((\operatorname{elementary}(\operatorname{t},\operatorname{x},\operatorname{y}))(\operatorname{X}))=((((\operatorname{elementaryK}(\operatorname{t},\operatorname{x})) \operatorname{X}) ((\operatorname{elementaryK}(\operatorname{t},\operatorname{x})))^{*})+(((\operatorname{elementaryL}(\operatorname{t},\operatorname{x},\operatorname{y})) \operatorname{X}) ((\operatorname{elementaryL}(\operatorname{t},\operatorname{x},\operatorname{y})))^{*}))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.elementary` (`✓ std3`).

*Citation.* Frederik vom Ende (2024). *A Sufficient Criterion for Divisibility of Quantum Channels*. DOI: [10.1063/5.0231812](https://doi.org/10.1063/5.0231812). URL: <https://arxiv.org/html/2407.17103v3>.

*Commentary.*

The map is precisely the sum of conjugations by the two source Kraus operators. For an orthogonal unit pair and 0 < t < 1 it is an actual trace-preserving completely positive map.

**Definition 1.7 (Exact elementary inverse).**

$$\forall (\operatorname{I}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{I}))][(\operatorname{DecidableEq}(\operatorname{I}))], \forall (\operatorname{t}:\mathbb{R}), \forall (\operatorname{x}:(\operatorname{I}\to\mathbb{C})), \forall (\operatorname{y}:(\operatorname{I}\to\mathbb{C})), \forall (\operatorname{X}:(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))), ((\operatorname{elementaryInverse}(\operatorname{t},\operatorname{x},\operatorname{y}))(\operatorname{X}))=((((1+((((\sqrt{(1-\operatorname{t})})^{-1}-1))\cdot((\operatorname{ketbra}(\operatorname{x},\operatorname{x}))))) \operatorname{X}) ((1+((((\sqrt{(1-\operatorname{t})})^{-1}-1))\cdot((\operatorname{ketbra}(\operatorname{x},\operatorname{x}))))))^{*})-((\frac{\operatorname{t}}{(1-\operatorname{t})})\cdot((((\operatorname{ketbra}(\operatorname{y},\operatorname{x})) \operatorname{X}) ((\operatorname{ketbra}(\operatorname{y},\operatorname{x})))^{*}))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.elementaryInverse` (`✓ std3`).

*Citation.* Frederik vom Ende (2024). *A Sufficient Criterion for Divisibility of Quantum Channels*. DOI: [10.1063/5.0231812](https://doi.org/10.1063/5.0231812). URL: <https://arxiv.org/html/2407.17103v3>.

*Commentary.*

Equation (2) defines this linear map. The theorem below proves both inverse identities in its stated range, together with trace preservation on every matrix.

**Definition 1.8 (Actual quantum channel).**

$$\forall (\operatorname{I}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{I}))][(\operatorname{DecidableEq}(\operatorname{I}))], \forall (\phi:((\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))\to_{l[\mathbb{C}]}(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C})))), (((\operatorname{CPTP}(\phi)))\Leftrightarrow((((\operatorname{CP}(\phi)))\land(\forall (\operatorname{X}:(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))), (\operatorname{tr}((\phi(\operatorname{X}))))=(\operatorname{tr}(\operatorname{X}))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.CPTP` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2024). *A Sufficient Criterion for Divisibility of Quantum Channels*. DOI: [10.1063/5.0231812](https://doi.org/10.1063/5.0231812). URL: <https://arxiv.org/html/2407.17103v3>.

*Commentary.*

CP is PhyslibLeaf.MatrixMap.IsCompletelyPositive, rather than positivity only on states or at a bounded amplification. The second conjunct is all-matrix trace preservation.

**Definition 1.9 (Elementary right division).**

$$\forall (\operatorname{I}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{I}))][(\operatorname{DecidableEq}(\operatorname{I}))], \forall (\phi:((\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))\to_{l[\mathbb{C}]}(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C})))), \forall (\operatorname{x}:(\operatorname{I}\to\mathbb{C})), \forall (\operatorname{y}:(\operatorname{I}\to\mathbb{C})), (((\operatorname{Divides}(\phi,\operatorname{x},\operatorname{y})))\Leftrightarrow(\exists (\operatorname{t}:\mathbb{R}), ((((0<\operatorname{t})\land(\operatorname{t}<1)))\land((\operatorname{CP}((\phi\circ(\operatorname{elementaryInverse}(\operatorname{t},\operatorname{x},\operatorname{y})))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.Divides` (`✓ std3`).

*Citation.* Frederik vom Ende (2024). *A Sufficient Criterion for Divisibility of Quantum Channels*. DOI: [10.1063/5.0231812](https://doi.org/10.1063/5.0231812). URL: <https://arxiv.org/html/2407.17103v3>.

*Commentary.*

The elementary channel is on the right of the composition. The same ordered pair is retained. The inverse formula is justified by the theorem when the pair is orthogonal and normalized.

**Definition 1.10 (Necessary Kraus-space criterion).**

$$\forall (\operatorname{I}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{I}))][(\operatorname{DecidableEq}(\operatorname{I}))], \forall (\operatorname{J}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{J}))], \forall (\operatorname{K}:(\operatorname{J}\to(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C})))), \forall (\operatorname{x}:(\operatorname{I}\to\mathbb{C})), \forall (\operatorname{y}:(\operatorname{I}\to\mathbb{C})), (((\operatorname{Necessary}(\operatorname{K},\operatorname{x},\operatorname{y})))\Leftrightarrow(\forall (\operatorname{G}:(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))), ((\forall (\operatorname{H}:(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))), ((\operatorname{H}\in(\operatorname{span}(\mathbb{C},(\operatorname{range}(\operatorname{K})))))\to((\operatorname{tr}(((\operatorname{H})^{*} \operatorname{G})))=0)))\to(\forall (\operatorname{j}:\operatorname{J}), \langle\operatorname{y},((((\operatorname{K}(\operatorname{j})))^{*} \operatorname{G})(\operatorname{x}))\rangle=0))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.Necessary` (`✓ std3`).

*Citation.* Frederik vom Ende (2024). *A Sufficient Criterion for Divisibility of Quantum Channels*. DOI: [10.1063/5.0231812](https://doi.org/10.1063/5.0231812). URL: <https://arxiv.org/html/2407.17103v3>.

*Commentary.*

Orthogonality is to the complex linear span of the Kraus family. Span induction equates this with tr(Kⱼ*G) = 0 for every Kraus index. The tests range over all complex matrices G and all Kraus indices j. This is Proposition 1's condition.

**Definition 1.11 (Sufficient Kraus-space criterion).**

$$\forall (\operatorname{I}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{I}))][(\operatorname{DecidableEq}(\operatorname{I}))], \forall (\operatorname{J}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{J}))], \forall (\operatorname{K}:(\operatorname{J}\to(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C})))), \forall (\operatorname{x}:(\operatorname{I}\to\mathbb{C})), \forall (\operatorname{y}:(\operatorname{I}\to\mathbb{C})), (((\operatorname{Sufficient}(\operatorname{K},\operatorname{x},\operatorname{y})))\Leftrightarrow((((\operatorname{Necessary}(\operatorname{K},\operatorname{x},\operatorname{y})))\land(\forall (\operatorname{G}:(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))), ((\forall (\operatorname{H}:(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))), ((\operatorname{H}\in(\operatorname{span}(\mathbb{C},(\operatorname{range}(\operatorname{K})))))\to((\operatorname{tr}(((\operatorname{H})^{*} \operatorname{G})))=0)))\to(\forall (\operatorname{j}:\operatorname{J}), \langle\operatorname{x},((((\operatorname{K}(\operatorname{j})))^{*} \operatorname{G})(\operatorname{x}))\rangle=0))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.Sufficient` (`✓ std3`).

*Citation.* Frederik vom Ende (2024). *A Sufficient Criterion for Divisibility of Quantum Channels*. DOI: [10.1063/5.0231812](https://doi.org/10.1063/5.0231812). URL: <https://arxiv.org/html/2407.17103v3>.

*Commentary.*

Theorem 1 adds the diagonal test ⟨x,Kⱼ*Gx⟩ = 0 to the necessary criterion. Its separate rank-reduction conclusion is not asserted here.

**Theorem 1.12 (The exact criterion and failure of the stronger converse).**

$$\forall (\operatorname{I}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{I}))][(\operatorname{DecidableEq}(\operatorname{I}))], ((2\leq(\operatorname{card}(\operatorname{I})))\to(((\forall (\phi:((\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))\to_{l[\mathbb{C}]}(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C})))), (((\operatorname{CPTP}(\phi)))\to(\exists (\operatorname{K}:((\operatorname{I}\times\operatorname{I})\to(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C})))), \sum_{\operatorname{j}\in(\operatorname{I}\times\operatorname{I})} (fun (\operatorname{X}:(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))) \mapsto (((\operatorname{K}(\operatorname{j})) \operatorname{X}) ((\operatorname{K}(\operatorname{j})))^{*}))=\phi)))\land(\forall (\operatorname{J}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{J}))], \forall (\operatorname{K}:(\operatorname{J}\to(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C})))), \forall (\phi:((\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))\to_{l[\mathbb{C}]}(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C})))), (((((\operatorname{CPTP}(\phi)))\land(\sum_{\operatorname{j}\in\operatorname{J}} (fun (\operatorname{X}:(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))) \mapsto (((\operatorname{K}(\operatorname{j})) \operatorname{X}) ((\operatorname{K}(\operatorname{j})))^{*}))=\phi)))\to(\forall (\operatorname{x}:(\operatorname{I}\to\mathbb{C})), \forall (\operatorname{y}:(\operatorname{I}\to\mathbb{C})), (((\operatorname{OrthogonalUnitPair}(\operatorname{x},\operatorname{y})))\to((((\operatorname{Necessary}(\operatorname{K},\operatorname{x},\operatorname{y})))\Leftrightarrow((\operatorname{Divides}(\phi,\operatorname{x},\operatorname{y})))))))))\land(\forall (\operatorname{J}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{J}))], \forall (\operatorname{K}:(\operatorname{J}\to(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C})))), \forall (\phi:((\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))\to_{l[\mathbb{C}]}(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C})))), (((((\operatorname{CPTP}(\phi)))\land(\sum_{\operatorname{j}\in\operatorname{J}} (fun (\operatorname{X}:(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))) \mapsto (((\operatorname{K}(\operatorname{j})) \operatorname{X}) ((\operatorname{K}(\operatorname{j})))^{*}))=\phi)))\to(((\exists (\operatorname{x}:(\operatorname{I}\to\mathbb{C})), \exists (\operatorname{y}:(\operatorname{I}\to\mathbb{C})), (((\operatorname{OrthogonalUnitPair}(\operatorname{x},\operatorname{y})))\land((\operatorname{Necessary}(\operatorname{K},\operatorname{x},\operatorname{y})))))\Leftrightarrow(\exists (\operatorname{x}:(\operatorname{I}\to\mathbb{C})), \exists (\operatorname{y}:(\operatorname{I}\to\mathbb{C})), (((\operatorname{OrthogonalUnitPair}(\operatorname{x},\operatorname{y})))\land((\operatorname{Divides}(\phi,\operatorname{x},\operatorname{y})))))))))\land(\forall (\operatorname{t}:\mathbb{R}), ((((0<\operatorname{t})\land(\operatorname{t}<1)))\to(\forall (\operatorname{x}:(\operatorname{I}\to\mathbb{C})), \forall (\operatorname{y}:(\operatorname{I}\to\mathbb{C})), (((\operatorname{OrthogonalUnitPair}(\operatorname{x},\operatorname{y})))\to((((\operatorname{CPTP}((\operatorname{elementary}(\operatorname{t},\operatorname{x},\operatorname{y})))))\land(((\operatorname{elementary}(\operatorname{t},\operatorname{x},\operatorname{y}))\circ(\operatorname{elementaryInverse}(\operatorname{t},\operatorname{x},\operatorname{y})))=\operatorname{id})\land(((\operatorname{elementaryInverse}(\operatorname{t},\operatorname{x},\operatorname{y}))\circ(\operatorname{elementary}(\operatorname{t},\operatorname{x},\operatorname{y})))=\operatorname{id})\land(\forall (\operatorname{X}:(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))), (\operatorname{tr}(((\operatorname{elementaryInverse}(\operatorname{t},\operatorname{x},\operatorname{y}))(\operatorname{X}))))=(\operatorname{tr}(\operatorname{X})))\land(\forall (\phi:((\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))\to_{l[\mathbb{C}]}(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C})))), (((((\operatorname{CPTP}(\phi)))\land((\operatorname{CP}((\phi\circ(\operatorname{elementaryInverse}(\operatorname{t},\operatorname{x},\operatorname{y}))))))))\to((((\operatorname{CPTP}((\phi\circ(\operatorname{elementaryInverse}(\operatorname{t},\operatorname{x},\operatorname{y}))))))\land(((\phi\circ(\operatorname{elementaryInverse}(\operatorname{t},\operatorname{x},\operatorname{y})))\circ(\operatorname{elementary}(\operatorname{t},\operatorname{x},\operatorname{y})))=\phi)))))))))))\land(\exists (\phi:((\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))\to_{l[\mathbb{C}]}(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C})))), (((\operatorname{CPTP}(\phi)))\land(\exists (\operatorname{x}:(\operatorname{I}\to\mathbb{C})), \exists (\operatorname{y}:(\operatorname{I}\to\mathbb{C})), (((\operatorname{OrthogonalUnitPair}(\operatorname{x},\operatorname{y})))\land((\operatorname{Divides}(\phi,\operatorname{x},\operatorname{y})))))\land(\forall (\operatorname{J}:\operatorname{Type}), \forall [(\operatorname{Fintype}(\operatorname{J}))], \forall (\operatorname{K}:(\operatorname{J}\to(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C})))), ((\sum_{\operatorname{j}\in\operatorname{J}} (fun (\operatorname{X}:(\operatorname{Matrix}(\operatorname{I},\operatorname{I},\mathbb{C}))) \mapsto (((\operatorname{K}(\operatorname{j})) \operatorname{X}) ((\operatorname{K}(\operatorname{j})))^{*}))=\phi)\to(\forall (\operatorname{u}:(\operatorname{I}\to\mathbb{C})), \forall (\operatorname{v}:(\operatorname{I}\to\mathbb{C})), (((\operatorname{OrthogonalUnitPair}(\operatorname{u},\operatorname{v})))\to(\neg(\operatorname{Sufficient}(\operatorname{K},\operatorname{u},\operatorname{v}))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.result` (`✓ std3`). ∎

*Resolves.* `Problems/vomende-2024-elementary-channel-divisibility` (proved) by `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"vomende-2024-elementary-channel-divisibility","declaration_gid":"D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2024). *A Sufficient Criterion for Divisibility of Quantum Channels*. DOI: [10.1063/5.0231812](https://doi.org/10.1063/5.0231812). URL: <https://arxiv.org/html/2407.17103v3>.

*Commentary.*

Every actual CPTP map has a finite Kraus representation. For every finite dimension at least two, the necessary criterion is equivalent to elementary division for the same ordered pair, and therefore also after existential quantification over pairs. These equivalences hold for every finite Kraus representation of an actual CPTP map. The last conjunct exhibits an actual CPTP map with an elementary division and no pair satisfying the stronger sufficient criterion, in every representation. Thus neither the fixed-pair nor the existential-pair converse of that sufficient criterion holds. The Proved resolution marker records this combined classification: both necessary-criterion equivalences are proved, while both assertions that elementary division implies the stronger sufficient criterion are refuted.

In input-first Choi coordinates let A = C(Φ) and Z = (|y⟩⟨x|)ᵀ ⊗ I. Hilbert–Schmidt orthogonality identifies the tests with ker A ⊆ ker(ZA Z*). If this inclusion holds, square roots factor as √B = C√A for B = ZA Z*. The operator norm bound gives B ≤ ‖C‖²A, and t = 1/(2(‖C‖²+1)) gives A−tB ≥ 0, including singular A. The exact Choi matrix of the residual is D(A−tB)D*, where D = Rᵀ ⊗ I and R is the inverse filter. Its congruence is invertible for 0 < t < 1.

For distinct basis vectors eᵣ,eₛ, take Φ = elementary(15/16,eᵣ,eₛ) and Q = elementary(3/4,eᵣ,eₛ). Direct Kraus algebra gives Q∘Q = Φ, hence Φ∘Q⁻¹ = Q. For any unit u, the diagonal sufficient test fails: the Hilbert–Schmidt tests Eᵣᵢ for i ≠ r force either uᵣ = 0 or all other coordinates to vanish, while a diagonal orthogonal test gives 1−|I||uᵣ|² = 0. Both alternatives contradict normalization when |I| ≥ 2. The intrinsic kernel criterion transfers this obstruction to every finite Kraus representation. These are finite-dimensional conclusions; no dimension-one pair or infinite-dimensional domination statement is included.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.CPTP`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.Divides`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.Necessary`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.OrthogonalUnitPair`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.Sufficient`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.elementary`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.elementaryInverse`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.elementaryK`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.elementaryL`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.ketbra`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.ketbra_star`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.result`
- Dependency: [D5/S3/Quantum/Recovery/ActualChannelAlgebra](../Recovery/ActualChannelAlgebra.md)
