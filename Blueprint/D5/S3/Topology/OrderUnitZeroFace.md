# Zero faces and a nilpotent unit direction

## Abstract

A linear map preserving every continuous positive zero face and annihilating the unit at second order already annihilates the unit.

Let E be any real normed vector space and A:OrderUnitNorm.Data(E). Thus C is a closed salient convex cone containing zero and u is its specified interior unit. Let T:E -> E be real linear. Neither continuity of T, completeness of E, finite dimension nor a nonzero-space assumption is required.

**Theorem 1.1 (Second-order unit nilpotence).**

Lean statement: `D5/S3/Topology/OrderUnitZeroFace.unit_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/OrderUnitZeroFace.unit_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every continuous real linear functional phi nonnegative on C satisfies phi(x)=0 implies phi(Tx)=0 for every x in C, and T(Tu)=0, then Tu=0.

Put v=Tu and f(t)=u+t v. Linearity and T(Tu)=0 give T(f(t))=v. If f(t) belongs to C but not its interior, OrderUnitNorm.Data.boundary_support supplies a continuous positive phi with phi(f(t))=0 and phi(u)>0. Zero-face preservation gives phi(v)=0. The affine equation then gives phi(u)=0, a contradiction.

Consequently f inverse(C) equals f inverse(interior(C)). It is both closed and open in the connected real line, and contains zero. It therefore equals the whole real line. Rescaling f(1/r) and f(-1/r) for each r>0 bounds the order norm of v by r. Definiteness of the existing order norm gives v=0. The new geometric step is the exclusion of every boundary contact, which makes the affine preimage open; no positive affine orbit is supplied as a premise.

For the arbitrary-dimensional quantum source, the intended substitution is the same supplied JB completion X, its own positive cone and unit, and T_a(x)=DX(a,x) for the continuous extension of the original D. For a continuous positive phi and c in the cone with phi(c)=0, the JB estimate 0<=c^2<=norm(c)c would give phi(c^2)=0. Positivity of a^2+lambda^2 c^2+2 lambda DX(a,c) for every real lambda would then give phi(DX(a,c))=0. The same NN identity at the unit would give T_a(T_a(u))=0. Faithfulness of the original unital embedding would return D(a,u)=0.

The NN transport itself uses only the supplied same-D restriction. Let e:E -> X be the original dense real linear isometry with e(u)=uX, and suppose DX(e(a),e(b))=e(D(a,b)). Original NN at b=u and S(a,u)=a give D(a,D(a,u))=S(a,a)-S(S(a,a),u)=0. Applying e gives DX(e(a),DX(e(a),uX))=0. The map x -> DX(x,DX(x,uX)) is continuous, so its zero set is closed and density extends this equality to every x in X. No completeness of E or change of D is used.

This theorem does not construct the JB positive cone or prove its square estimate, transport the original NN identity through the dense embedding, or establish those original consumer hypotheses. In particular it does not establish the full Jordan Leibniz conclusion, original associator rigidity, a bidual representation, or any physical preparation or dynamics. All continuous positive functionals, including zero, occur in the hypothesis; there is no density assumption on the physical preparation family. The argument uses the existing Hahn-Banach boundary support and order norm, and makes no literature novelty claim.

## References

- Truth anchor: `D5/S3/Topology/OrderUnitZeroFace.unit_eq_zero`
- Dependency: [D5/S3/Topology/OrderUnitNorm](OrderUnitNorm.md)
