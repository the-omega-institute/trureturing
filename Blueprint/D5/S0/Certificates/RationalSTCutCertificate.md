# RationalSTCutCertificate

## Abstract

Exact flow conservation and capacity checks certify a global minimum cut.

Vertex is an arbitrary finite type. capacity is Vertex to Vertex to Q; source and sink are Vertex to Q; side is Vertex to Bool. All sums cover the entire finite carrier. True labels are on the source side.

**Definition 1.1 (Directed cut energy).**

$$\forall Vertex, capacity, source, sink, side, (\operatorname{stCutValue}(capacity, source, sink, side)) = ((\sum_{i} (\operatorname{ite}(\operatorname{apply}(side, i), \operatorname{sink}(i), \operatorname{source}(i)))) + (\sum_{i} (\sum_{j} (\operatorname{ite}(((\operatorname{apply}(side, i)) = (true)) \land ((\operatorname{apply}(side, j)) = (false)), \operatorname{capacity}(i, j), 0)))))$$

*Formalization.* `D5/S0/Certificates/RationalSTCutCertificate.stCutValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source is fixed on the true side and the sink on the false side. All vertex assignments are allowed.

**Definition 1.2 (Untrusted flow and cut data).**

Lean statement: `D5/S0/Certificates/RationalSTCutCertificate.STCutCertificate`

*Formalization.* `D5/S0/Certificates/RationalSTCutCertificate.STCutCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fields are internal : Vertex to Vertex to Q; fromSource and toSink : Vertex to Q; side : Vertex to Bool. No proof or claimed optimality field is supplied.

**Definition 1.3 (Value leaving the source).**

$$\forall Vertex, certificate, (\operatorname{flowValue}(certificate)) = (\sum_{i} (\operatorname{fromSource}(certificate, i)))$$

*Formalization.* `D5/S0/Certificates/RationalSTCutCertificate.flowValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The flow value is recomputed from terminal flows.

**Definition 1.4 (Capacity, conservation and equality).**

$$\forall Vertex, capacity, source, sink, certificate, (\operatorname{ValidSTCutCertificate}(capacity, source, sink, certificate)) \Leftrightarrow ((\forall i, j, ((0) \le (\operatorname{internal}(certificate, i, j))) \land ((\operatorname{internal}(certificate, i, j)) \le (\operatorname{capacity}(i, j)))) \land (\forall i, ((0) \le (\operatorname{fromSource}(certificate, i))) \land ((\operatorname{fromSource}(certificate, i)) \le (\operatorname{source}(i)))) \land (\forall i, ((0) \le (\operatorname{toSink}(certificate, i))) \land ((\operatorname{toSink}(certificate, i)) \le (\operatorname{sink}(i)))) \land (\forall i, ((\operatorname{fromSource}(certificate, i)) + (\sum_{j} (\operatorname{internal}(certificate, j, i)))) = ((\operatorname{toSink}(certificate, i)) + (\sum_{j} (\operatorname{internal}(certificate, i, j))))) \land ((\operatorname{stCutValue}(capacity, source, sink, \operatorname{side}(certificate))) = (\operatorname{flowValue}(certificate))))$$

*Formalization.* `D5/S0/Certificates/RationalSTCutCertificate.ValidSTCutCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each capacity condition and each conservation equation is checked on the actual finite arrays; the supplied cut must match the flow value.

**Definition 1.5 (Executable exact check).**

$$\forall Vertex, capacity, source, sink, certificate, (\operatorname{checkSTCutCertificate}(capacity, source, sink, certificate)) = (\operatorname{decide}(\operatorname{ValidSTCutCertificate}(capacity, source, sink, certificate)))$$

*Formalization.* `D5/S0/Certificates/RationalSTCutCertificate.checkSTCutCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

No floating acceptance tolerance or exhaustive Boolean search is used by the checker.

**Theorem 1.6 (Acceptance reflection).**

$$\forall Vertex, capacity, source, sink, certificate, ((\operatorname{checkSTCutCertificate}(capacity, source, sink, certificate)) = (true)) \Leftrightarrow (\operatorname{ValidSTCutCertificate}(capacity, source, sink, certificate))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalSTCutCertificate.checkSTCutCertificate_eq_true_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Connects Boolean acceptance to the exact finite arithmetic contract.

**Theorem 1.7 (Conservation across any cut).**

$$\forall Vertex, certificate, side, (\forall i, ((\operatorname{fromSource}(certificate, i)) + (\sum_{j} (\operatorname{internal}(certificate, j, i)))) = ((\operatorname{toSink}(certificate, i)) + (\sum_{j} (\operatorname{internal}(certificate, i, j))))) \Rightarrow ((\operatorname{flowValue}(certificate)) = ((\sum_{i} (\operatorname{ite}(\operatorname{apply}(side, i), \operatorname{toSink}(certificate, i), \operatorname{fromSource}(certificate, i)))) + (\sum_{i} (\sum_{j} ((\operatorname{internal}(certificate, i, j)) \cdot ((\operatorname{ite}(\operatorname{apply}(side, i), 1, 0)) - (\operatorname{ite}(\operatorname{apply}(side, j), 1, 0))))))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalSTCutCertificate.flow_cut_accounting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only flow conservation is required by this identity. Opposite directed terms cancel when summing over all vertices.

**Theorem 1.8 (Global weak flow-cut duality).**

$$\forall Vertex, capacity, source, sink, certificate, side, ((\forall i, j, ((0) \le (\operatorname{internal}(certificate, i, j))) \land ((\operatorname{internal}(certificate, i, j)) \le (\operatorname{capacity}(i, j)))) \land (\forall i, (\operatorname{fromSource}(certificate, i)) \le (\operatorname{source}(i))) \land (\forall i, (\operatorname{toSink}(certificate, i)) \le (\operatorname{sink}(i))) \land (\forall i, ((\operatorname{fromSource}(certificate, i)) + (\sum_{j} (\operatorname{internal}(certificate, j, i)))) = ((\operatorname{toSink}(certificate, i)) + (\sum_{j} (\operatorname{internal}(certificate, i, j)))))) \Rightarrow ((\operatorname{flowValue}(certificate)) \le (\operatorname{stCutValue}(capacity, source, sink, side)))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalSTCutCertificate.flowValue_le_every_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower bound covers every cut, including those never visited by a solver.

**Theorem 1.9 (Attained minimum certificate).**

$$\forall Vertex, capacity, source, sink, certificate, ((\operatorname{checkSTCutCertificate}(capacity, source, sink, certificate)) = (true)) \Rightarrow (((\operatorname{stCutValue}(capacity, source, sink, \operatorname{side}(certificate))) = (\operatorname{flowValue}(certificate))) \land (\forall side, (\operatorname{flowValue}(certificate)) \le (\operatorname{stCutValue}(capacity, source, sink, side))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalSTCutCertificate.checkSTCutCertificate_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A single accepted pair proves that its cut is a global minimum; no optimal flow premise or algorithmic discovery theorem is assumed.

## References

- Truth anchor: `D5/S0/Certificates/RationalSTCutCertificate.STCutCertificate`
- Truth anchor: `D5/S0/Certificates/RationalSTCutCertificate.ValidSTCutCertificate`
- Truth anchor: `D5/S0/Certificates/RationalSTCutCertificate.checkSTCutCertificate`
- Truth anchor: `D5/S0/Certificates/RationalSTCutCertificate.checkSTCutCertificate_eq_true_iff`
- Truth anchor: `D5/S0/Certificates/RationalSTCutCertificate.checkSTCutCertificate_sound`
- Truth anchor: `D5/S0/Certificates/RationalSTCutCertificate.flowValue`
- Truth anchor: `D5/S0/Certificates/RationalSTCutCertificate.flowValue_le_every_cut`
- Truth anchor: `D5/S0/Certificates/RationalSTCutCertificate.flow_cut_accounting`
- Truth anchor: `D5/S0/Certificates/RationalSTCutCertificate.stCutValue`
- Dependency: [D5/S0/Certificates/LinearObjectiveDual](LinearObjectiveDual.md)
