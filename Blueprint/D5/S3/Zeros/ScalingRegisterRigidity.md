# Scaling-Register Rigidity

## Abstract

Same-germ and same-total-code continuations exclude nontrivial scaling registers.

**Definition 1.1 (A scaling register is a nontrivial coordinatewise exponential).**

Lean statement: `D5/S3/Zeros/ScalingRegisterRigidity.ScalingRegister`

*Formalization.* `D5/S3/Zeros/ScalingRegisterRigidity.ScalingRegister` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a ledger length ell and factor family R, ScalingRegister(ell,R) means that some g gives R(s,a)=exp(g(s)ell(a)) for every s and a, and that R(s,a) differs from one at some coordinate. This is the formal carrier of Definition 23.2's dependence and nontriviality clauses.

Honest scope declaration: the predicate does not internalize "unrecorded" ledger custody. Address independence is the formal proxy for an explicit global ledger factor; the institutional classification itself remains at the narrative layer.

**Theorem 1.2 (A nontrivial register is not address-independent).**

$$\forall A\,[\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ \forall R:\mathbb{C}\to A\to\mathbb{C},\ (\exists a,\ell(a)\neq0)\land\operatorname{ScalingRegister}(\ell,R)\Rightarrow\neg\forall s,a,b,\ R(s,a)=R(s,b).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ScalingRegisterRigidity.scaling_register_not_address_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the zero address every exponential register equals one. Address independence would therefore make every coordinate one, contradicting the explicit nontrivial witness. The supplied nontrivial-length premise records that the ledger itself has a genuine coordinate direction.

**Theorem 1.3 (Same germ and same total code exclude scaling registers).**

$$\begin{gathered}U\subseteq\mathbb{C},\ f,\widetilde f:\mathbb{C}\to\mathbb{C},\quad \operatorname{AnalyticOnNhd}(f,U),\quad\operatorname{AnalyticOnNhd}(\widetilde f,U),\\\operatorname{IsPreconnected}(U),\quad s_0\in U,\ f=_{\operatorname{nhds}(s_0)}\widetilde f,\\T:\operatorname{TotalCode}(D,Q,L)\to\operatorname{TotalCode}(D,Q,L),\quad X:\operatorname{TotalCode}(D,Q,L),\quad T(X)=X,\\A\ [\operatorname{AddMonoid}(A)],\quad \ell:A\to_{+}\mathbb{R},\quad R:\mathbb{C}\to A\to\mathbb{C},\\\operatorname{ScalingRegister}(\ell,R)\Rightarrow\exists s\in U,\ \widetilde f(s)\neq f(s),\\\operatorname{ScalingRegister}(\ell,R)\Rightarrow T(X)\neq X\end{gathered}\quad\Rightarrow\quad\operatorname{NoScalingRegister}(\ell,R).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ScalingRegisterRigidity.same_germ_same_total_code_has_no_scaling_register` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The analytic field of the certificate consumes the same-germ premise through analytic_continuation_unique, so a register cannot produce the required pointwise change on U. The total-code field consumes T(X)=X through no_hidden_register: a genuine object change must expose a changed data, rules, or ledger component, each impossible after the code equality is rewritten.

Honest scope declaration: Lean does not derive from complex analysis that every unrecorded register changes both the continued function and the represented object. Those two faithfulness bridges are explicit premises. The theorem is closed at the analytic layer plus the definitional TotalCode reading of criterion 7.2; it does not claim an ontological proof beyond those typed inputs.

**Theorem 1.4 (The scaling-register predicate has a concrete witness).**

$$\operatorname{ScalingRegister}\!\left(\operatorname{castAddHom}_{\mathbb{R}},\ (s,n)\mapsto\exp(\pi i n)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ScalingRegisterRigidity.integer_scaling_register_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the integer ledger, the cast-to-real length and the factor exp(pi i n) satisfy the register shape, while n=1 evaluates to minus one rather than one. This kernel-checked counterexample-style witness prevents the main exclusion theorem from succeeding merely because ScalingRegister is empty.
