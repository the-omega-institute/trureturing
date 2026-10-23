# Native coordinates in integer valuations

## Abstract

Reversed bound coordinates align native snoc with the backend binder head.

For arbitrary natural m and n, v:Fin m->Nat is the free valuation and xs:Fin n->Nat is the bound valuation. NatTuple(r) abbreviates Fin r->Nat. environment(v,xs) is reverse(List.ofFn(cast o xs)) followed by List.ofFn(cast o v). Thus a free coordinate i lies at n+i and a bound coordinate i lies at n-1-i. The sum type distinguishes them even if the numerical indices coincide.

basis(k) is an affine expression with coefficient one at k, zero elsewhere and constant zero. It is built recursively with consCoeff; missing valuation entries contribute zero. Native coordinates are proved present by environment_lookup. For m=0 or n=0 the corresponding domain is empty, and when both vanish the environment is the empty list.

**Theorem 1.1 (The affine coordinate reads its list entry).**

$$\forall k \in Nat,\; \forall env \in \operatorname{List}\left(Int\right),\; \operatorname{eval}\left(\operatorname{basis}\left(k\right), env\right) = \operatorname{getD}\left(\operatorname{getOptional}\left(env, k\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/NatPresburgerEnvironment.eval_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

Induction on k, generalized over the list, removes one affine coefficient and one list head together. The nil branch proves the same zero-default convention at every index.

**Theorem 1.2 (Native sum coordinates are exact).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall v \in \operatorname{NatTuple}\left(m\right),\; \forall xs \in \operatorname{NatTuple}\left(n\right),\; \forall i \in \operatorname{Sum}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right),\; \operatorname{getD}\left(\operatorname{getOptional}\left(\operatorname{environment}\left(v, xs\right), \operatorname{position}\left(i\right)\right), 0\right) = \operatorname{cast}\left(\operatorname{elim}\left(v, xs, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/NatPresburgerEnvironment.environment_lookup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

The free branch uses lookup in the right part of an appended list. The bound branch uses lookup in the left part and the reversal index identity. No positive-context assumption is required.

**Theorem 1.3 (Appending a native bound value creates the integer head).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall v \in \operatorname{NatTuple}\left(m\right),\; \forall xs \in \operatorname{NatTuple}\left(n\right),\; \forall x \in Nat,\; \operatorname{environment}\left(v, \operatorname{snoc}\left(xs, x\right)\right) = \operatorname{cons}\left(\operatorname{cast}\left(x\right), \operatorname{environment}\left(v, xs\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/NatPresburgerEnvironment.environment_snoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

The supplied List.ofFn snoc identity, followed by reversal and append normalization, gives this list equality. It aligns the native universal binder with the integer de Bruijn convention.

## References

- Truth anchor: `D5/S0/Computability/NatPresburgerEnvironment.environment_lookup`
- Truth anchor: `D5/S0/Computability/NatPresburgerEnvironment.environment_snoc`
- Truth anchor: `D5/S0/Computability/NatPresburgerEnvironment.eval_basis`
- Dependency: [D5/S0/Computability/PresburgerSyntax](PresburgerSyntax.md)
