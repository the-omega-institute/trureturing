# No Invisible Register

## Abstract

Total-code-preserving transformations cannot hide object changes.

**Theorem 1.1 (Preserving the total code preserves the object).**

$$\forall D,R,L,\quad \left[\forall f:\operatorname{TotalCode}(D,R,L)\to\operatorname{TotalCode}(D,R,L),\ \left(\forall X,\ \operatorname{data}(f(X))=\operatorname{data}(X)\right)\land \left(\forall X,\ \operatorname{rules}(f(X))=\operatorname{rules}(X)\right)\land \left(\forall X,\ \operatorname{ledger}(f(X))=\operatorname{ledger}(X)\right)\Rightarrow\forall X,\ f(X)=X\right]\land \left[\forall f,X,\ f(X)\neq X\Rightarrow \operatorname{data}(f(X))\neq\operatorname{data}(X)\lor \operatorname{rules}(f(X))\neq\operatorname{rules}(X)\lor \operatorname{ledger}(f(X))\neq\operatorname{ledger}(X)\right].$$

*Proof.* Machine-checked in Lean as `D5/S0/Conventions/TotalCode.no_hidden_register` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The semantic kernel-identity criterion is represented here by Lean structure equality, not claimed as a proof of an ontological identity criterion. Extensionality proves both the preservation clause and its componentwise dual. This is the C3a identity pillar announced for use in 23.4.
