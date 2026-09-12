# Formula rewriting

## Abstract

General formula rewriting, occurrence origins, support congruence, universal closure and language compatibility.

Let L be any first-order language, with arbitrary relation arities, free-variable types and binder depths. Rewriting acts on all eight formula constructors: truth, falsity, positive and negative relations, conjunction, disjunction, universal and existential quantification. A quantifier lifts the term assignment by fixing bound zero and shifting the images of older variables. This action preserves logical connectives, has identity and composition laws, and preserves injectivity of bound and free renamings.

The occurrence-origin theorem LO.FirstOrder.Semiformula.fvar?_rew uses decidable equality on both free-variable types. If x occurs freely in the rewritten formula, then x occurs in the image of some bound variable, or in the image of a free variable that actually occurs in the original formula. The assertion is one-way: it does not claim that every image of a bound variable contributes an occurrence.

**Lemma 1.1 (Agreement on the actual support suffices).**

$$\operatorname{act}\left(\mathit{omega1}, \mathit{phi}\right) = \operatorname{act}\left(\mathit{omega2}, \mathit{phi}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcSyntax/FormulaRewriting.rew_eq_of_funEqOn` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

Assume decidable equality on the source free-variable type. The two term assignments agree on every bound variable and on the free variables in phi.FVar?. Their formula actions are equal, without agreement assumptions on other free variables. The source and target depths and target free-variable type are arbitrary.

For a proposition with natural-number free variables, fvSup bounds its finite support. The formula univCl' first fixes every index below this bound as a bound variable, then universally quantifies the resulting vector. The theorem LO.FirstOrder.Semiformula.fvarList_univCl' states that phi.univCl'.freeVariables = ∅. Its proof uses not_fvar?_fixitr_fvSup: the occurrence-origin alternatives are impossible because the original bound context is Fin 0 and every occurring free variable lies below fvSup.

**Lemma 1.2 (Conversion to an empty free-variable type is faithful).**

$$\operatorname{emb}\left(\operatorname{toEmpty}\left(\mathit{phi}, \mathit{hp}\right)\right) = \mathit{phi}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcSyntax/FormulaRewriting.emb_toEmpty` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For every L, xi, n, decidable equality on xi, phi : Semiformula L xi n and hp : phi.freeVariables = ∅, embedding phi.toEmpty hp back into xi yields phi. The recursive conversion retains the same empty-support guard under both quantifiers. At each binder, lifting the embedding map is the embedding at the successor depth: bound zero and successors agree separately, and there are no Empty free variables. The original subformula is recovered by the induction hypothesis.

The data operation univCl returns a Sentence by applying toEmpty to univCl'. A proof of empty support justifies this conversion; the result contains no free-variable payload.

**Lemma 1.3 (Language maps commute with term assignment).**

$$\operatorname{lMap}\left(\mathit{Phi}, \operatorname{act}\left(\operatorname{bind}\left(b, e\right), \mathit{phi}\right)\right) = \operatorname{act}\left(\operatorname{bind}\left(\operatorname{compose}\left(\operatorname{termLMap}\left(\mathit{Phi}\right), b\right), \operatorname{compose}\left(\operatorname{termLMap}\left(\mathit{Phi}\right), e\right)\right), \operatorname{lMap}\left(\mathit{Phi}, \mathit{phi}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcSyntax/FormulaRewriting.lMap_bind` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

For arbitrary languages L1 and L2, a language homomorphism Phi, bound assignment b, free assignment e and formula phi, mapping the language after assignment equals assignment by the mapped terms after mapping phi. All source and target variable types and depths remain arbitrary. Under either quantifier, term language mapping commutes with bound shifting and the lifted vector assignments coincide.

The following anonymous Lean terms express the general data operations and consequences. All language-map terms use variable {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {Φ : L₁ →ᵥ L₂} in namespace LO.FirstOrder.Semiformula.

free: example (φ : Semiproposition L (n + 1)) : Semiproposition L n := Rewriting.free φ

shift: example (φ : Semiproposition L n) : Semiproposition L n := Rewriting.shift φ

rew_rel_eq_comp: example (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} : ω ▹ rel r v = rel r (ω ∘ v) := rfl

rew_nrel_eq_comp: example (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} : ω ▹ nrel r v = nrel r (ω ∘ v) := rfl

instLawfulSyntacticRewritingSemiproposition: example : LawfulSyntacticRewriting L (Semiproposition L) where

instCoeSemisentenceSemiproposition: example : Coe (Semisentence L n) (Semiproposition L n) := ⟨Rewriting.emb (ξ := ℕ)⟩

rew_eq_of_funEqOn₀: example [DecidableEq ξ₁] {ω₁ ω₂ : Rew L ξ₁ 0 ξ₂ n₂} {φ : Semiformula L ξ₁ 0} (hf : Function.funEqOn (φ.FVar?) (ω₁ ∘ Semiterm.fvar) (ω₂ ∘ Semiterm.fvar)) : ω₁ ▹ φ = ω₂ ▹ φ := rew_eq_of_funEqOn (fun x ↦ Fin.elim0 x) hf

lMap_subst: example (w : Fin k → Semiterm L₁ ξ n) (φ : Semiformula L₁ ξ k) : lMap Φ (φ ⇜ w) = (lMap Φ φ)⇜(Semiterm.lMap Φ ∘ w) := lMap_bind _ _ _

lMap_shift: example (φ : Semiproposition L₁ n) : lMap Φ (@Rew.shift L₁ n ▹ φ) = @Rew.shift L₂ n ▹ lMap Φ φ := lMap_bind _ _ _

lMap_free: example (φ : Semiproposition L₁ (n + 1)) : lMap Φ (@Rew.free L₁ n ▹ φ) = @Rew.free L₂ n ▹ lMap Φ φ := by simp [Rew.free, lMap_bind, Function.comp_def, Matrix.comp_vecConsLast]

lMap_emb: example {ο : Type _} [IsEmpty ο] (φ : Semiformula L₁ ο n) : (lMap Φ (Rewriting.emb φ : Semiformula L₁ ξ n)) = Rewriting.emb (lMap Φ φ) := lMap_bind _ _ _

The source theorem complexity_rew states that every formula rewriting preserves complexity. Its induction argument belongs with the finite-derivation calculus: both quantified clauses of Derivation.eta recurse on phi.free and use phi.complexity as their termination measure. That calculus and this complexity lemma are outside the present collection.

The original mathematical bodies are from FormalizedFormalLogic/Foundation, Foundation/FirstOrder/Basic/Syntax/Rew.lean, revision 30a16ffa93d79d73ab4d02427fa00f50e039bf29. Copyright remains with the Foundation contributors. The Apache-2.0 license and notices are in Library/ConceptDynamics/foundation2026firstorder.md. The action helpers are arranged in one owner and the embedding proof uses a local comparison under each binder. An equivalent interface in the repository's pinned Mathlib replaces this source when a faithful carrier bridge is available.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ZfcSyntax/FormulaRewriting.emb_toEmpty`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcSyntax/FormulaRewriting.lMap_bind`
- Truth anchor: `D5/S3/ConceptDynamics/ZfcSyntax/FormulaRewriting.rew_eq_of_funEqOn`
- Dependency: [D5/S3/ConceptDynamics/ZfcFiniteCollections/Finset](../ZfcFiniteCollections/Finset.md)
- Dependency: [D5/S3/ConceptDynamics/ZfcSyntax/FormulaTwo](FormulaTwo.md)
- Dependency: [D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour](../ZfcTermRewriting/RewFour.md)
