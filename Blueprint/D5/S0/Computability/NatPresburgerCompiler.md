# A structural Nat-to-Int semantic compiler

## Abstract

Every native binder receives its own nonnegative integer guard.

BF(m,n) abbreviates presburger.BoundedFormula (Fin m) n, and NatTerm(m,n) abbreviates presburger.Term (Fin m sum Fin n). Bounded refers to the finite variable context, not to a numerical bound on the quantified values. All m,n, including zero, all natural valuations and every finite formula are in scope.

compileTerm maps variables to basis(position i), zero and one to integer affine constants, and addition to affine addition. The native language has no relation symbols: the relation branch eliminates the Empty relation type, with no fallback. Term induction connects affine evaluation to the integer cast of the original native Term.realize.

compile maps falsum to false; equality s=t to the conjunction 0<=s-t and 0<=-(s-t); implication to not-left or right. Each native all body becomes the backend all of the implication from 0<=head to compile(body). The child is compiled in its own larger native context; it is not shifted a second time.

The nonnegative guard is added at every binder, including binders occurring under negation and in arbitrarily alternating formulas. A guard only at the outermost binder would change Nat semantics. Native existential and negation constructions already use implication and all, so the same structural proof covers them. No bound on numeral size, context size or quantifier nesting is assumed.

**Theorem 1.1 (Exact native term values).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall t \in \operatorname{NatTerm}\left(m, n\right),\; \forall v \in \operatorname{NatTuple}\left(m\right),\; \forall xs \in \operatorname{NatTuple}\left(n\right),\; \operatorname{eval}\left(\operatorname{compileTerm}\left(t\right), \operatorname{environment}\left(v, xs\right)\right) = \operatorname{cast}\left(\operatorname{realizeTerm}\left(t, \operatorname{elim}\left(v, xs\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/NatPresburgerCompiler.compile_term_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

The variable case composes eval_basis with environment_lookup. Zero, one and addition use the native function interpretation and upstream affine evaluation laws. This is a native structural semantic bridge; it does not reprove Cooper elimination.

**Theorem 1.2 (Exact native formula semantics).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall p \in \operatorname{BF}\left(m, n\right),\; \forall v \in \operatorname{NatTuple}\left(m\right),\; \forall xs \in \operatorname{NatTuple}\left(n\right),\; (\operatorname{holds}\left(\operatorname{compile}\left(p\right), \operatorname{environment}\left(v, xs\right)\right)) \iff (\operatorname{Realize}\left(p, v, xs\right))$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/NatPresburgerCompiler.compile_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

Formula induction treats equality by term preservation and injectivity of the Nat cast. At all, environment_snoc aligns the new coordinate. A natural x supplies a nonnegative integer cast; conversely a guarded integer z supplies z.toNat with cast(z.toNat)=z. This proves both quantified directions, and induction preserves every implication, negation and alternation.

## References

- Truth anchor: `D5/S0/Computability/NatPresburgerCompiler.compile_correct`
- Truth anchor: `D5/S0/Computability/NatPresburgerCompiler.compile_term_correct`
- Dependency: [D5/S0/Computability/NatPresburgerEnvironment](NatPresburgerEnvironment.md)
