# Scaling-Register Rigidity

## Abstract

Typed realization carries analytic uniqueness through the registered action to conditional total-code rigidity.

**Definition 1.1 (A scaling register is a nontrivial coordinatewise exponential).**

Lean statement: `D5/S3/Zeros/ScalingRegisterRigidity.ScalingRegister`

*Formalization.* `D5/S3/Zeros/ScalingRegisterRigidity.ScalingRegister` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a ledger length ell and factor family R, ScalingRegister(ell,R) means that some g gives R(s,a)=exp(g(s)ell(a)) for every s and a, and that R(s,a) differs from one at some coordinate. This is the formal carrier of Definition 23.2's dependence and nontriviality clauses.

Honest scope declaration: the predicate does not internalize "unrecorded" ledger custody. Address independence is the formal proxy for an explicit global ledger factor; the institutional classification itself remains at the narrative layer.

**Theorem 1.2 (A nontrivial register is not address-independent).**

$$\forall A\,[\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ \forall R:\mathbb{C}\to A\to\mathbb{C},\ \operatorname{ScalingRegister}(\ell,R)\Rightarrow\neg\forall s,a,b,\ R(s,a)=R(s,b).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ScalingRegisterRigidity.scaling_register_not_address_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the zero address every exponential register equals one. Address independence would therefore make every coordinate one, contradicting the explicit nontrivial witness.

**Definition 1.3 (A register acts on the tagged data field).**

Lean statement: `D5/S3/Zeros/ScalingRegisterRigidity.applyRegister`

*Formalization.* `D5/S3/Zeros/ScalingRegisterRigidity.applyRegister` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For data X.data(a,s), applyRegister(R,X) replaces that value by R(s,a)X.data(a,s), while preserving the rules and ledger fields.

**Theorem 1.4 (A nontrivial register changes nowhere-zero data).**

$$\left(\forall a,s,\ X_{\operatorname{data}}(a,s)\neq0\right)\land\left(\exists s,a,\ R(s,a)\neq1\right)\Rightarrow\operatorname{applyRegister}(R,X)\neq X.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ScalingRegisterRigidity.applyRegister_ne_of_nontrivial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the nontrivial witness, equality of total codes would equate the data values R(s,a)X.data(a,s) and X.data(a,s). Cancelling the explicitly nonzero data value forces R(s,a)=1, a contradiction.

**Definition 1.5 (Realization projects object data and carries register actions).**

Lean statement: `D5/S3/Zeros/ScalingRegisterRigidity.RealizesAt`

*Formalization.* `D5/S3/Zeros/ScalingRegisterRigidity.RealizesAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RealizesAt(a,X,f) records both that the declared address projection of X.data reads as f and that the same projection sends applyRegister(R,X) to the pointwise product R(s,a)f(s). The compatibility clause is a defining model law, not a bridge assumption derived from mathlib.

**Theorem 1.6 (Realized same germ and same total code force a trivial register).**

$$\begin{gathered}U\subseteq\mathbb{C},\ f,\widetilde f:\mathbb{C}\to\mathbb{C},\quad \operatorname{AnalyticOnNhd}(f,U),\quad\operatorname{AnalyticOnNhd}(\widetilde f,U),\\\operatorname{IsPreconnected}(U),\quad s_0\in U,\ f=_{\operatorname{nhds}(s_0)}\widetilde f,\\R:\mathbb{C}\to A\to\mathbb{C},\quad X:\operatorname{TotalCode}(A\to\mathbb{C}\to\mathbb{C},Q,L),\\\operatorname{RealizesAt}(a,X,f),\quad\operatorname{RealizesAt}(a,\operatorname{applyRegister}(R,X),\widetilde f),\\\forall a,s,\ X_{\operatorname{data}}(a,s)\neq0,\quad\operatorname{applyRegister}(R,X)=X\end{gathered}\quad\Rightarrow\quad\left(f=\widetilde f\text{ on }U\right)\land\left(\forall s,\ \widetilde f(s)=R(s,a)f(s)\right)\land\left(\forall s,a,\ R(s,a)=1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ScalingRegisterRigidity.realized_same_germ_same_total_code_forces_trivial_register` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Analytic continuation uniqueness identifies the two readings on U. The RealizesAt model law then identifies the registered reading pointwise with R(s,a)f(s). Finally, a non-one witness and nowhere-zero data would produce an applyRegister object change, contradicting equal total code.

Honest scope declaration: this is conditional on the typed realization relations and does not internalize unrecorded ledger custody.

**Theorem 1.7 (Realized code-preserving continuations exclude scaling registers).**

$$\operatorname{RealizesAt}(a,X,f)\land\operatorname{RealizesAt}(a,\operatorname{applyRegister}(R,X),\widetilde f)\land\text{ same germ}\land\text{ same total code}\Rightarrow\neg\operatorname{ScalingRegister}(\ell,R).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ScalingRegisterRigidity.realized_same_germ_same_total_code_excludes_scaling_register` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The realized rigidity theorem makes R pointwise one, contradicting the nontriviality witness required by ScalingRegister. This is the explicit ScalingRegister exclusion and retains every realization and code premise.

**Theorem 1.8 (The scaling-register predicate has a concrete witness).**

$$\operatorname{ScalingRegister}\!\left(\operatorname{castAddHom}_{\mathbb{R}},\ (s,n)\mapsto\exp(\pi i n)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ScalingRegisterRigidity.integer_scaling_register_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the integer ledger, the cast-to-real length and the factor exp(pi i n) satisfy the register shape, while n=1 evaluates to minus one rather than one. This kernel-checked counterexample-style witness prevents the main exclusion theorem from succeeding merely because ScalingRegister is empty.
