using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ZfcSyntax;

internal sealed class FormulaRewritingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/ZfcSyntax/FormulaRewriting.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/foundation2026firstorder");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "General formula rewriting, occurrence origins, support congruence, universal closure and language compatibility.",
        H("Formula rewriting"),
        Blocks(
            Paragraph(Text("Let L be any first-order language, with arbitrary relation arities, free-variable types and binder depths. Rewriting acts on all eight formula constructors: truth, falsity, positive and negative relations, conjunction, disjunction, universal and existential quantification. A quantifier lifts the term assignment by fixing bound zero and shifting the images of older variables. This action preserves logical connectives, has identity and composition laws, and preserves injectivity of bound and free renamings.")),
            Paragraph(Text("The occurrence-origin theorem LO.FirstOrder.Semiformula.fvar?_rew uses decidable equality on both free-variable types. If x occurs freely in the rewritten formula, then x occurs in the image of some bound variable, or in the image of a free variable that actually occurs in the original formula. The assertion is one-way: it does not claim that every image of a bound variable contributes an occurrence.")),
            Entry("support-congruence", "rew_eq_of_funEqOn", "Agreement on the actual support suffices",
                Equal(Act(Id("omega1"), Id("phi")), Act(Id("omega2"), Id("phi"))),
                "Assume decidable equality on the source free-variable type. The two term assignments agree on every bound variable and on the free variables in phi.FVar?. Their formula actions are equal, without agreement assumptions on other free variables. The source and target depths and target free-variable type are arbitrary."),
            Paragraph(Text("For a proposition with natural-number free variables, fvSup bounds its finite support. The formula univCl' first fixes every index below this bound as a bound variable, then universally quantifies the resulting vector. The theorem LO.FirstOrder.Semiformula.fvarList_univCl' states that phi.univCl'.freeVariables = ∅. Its proof uses not_fvar?_fixitr_fvSup: the occurrence-origin alternatives are impossible because the original bound context is Fin 0 and every occurring free variable lies below fvSup.")),
            Entry("empty-round-trip", "emb_toEmpty", "Conversion to an empty free-variable type is faithful",
                Equal(Call("emb", Call("toEmpty", Id("phi"), Id("hp"))), Id("phi")),
                "For every L, xi, n, decidable equality on xi, phi : Semiformula L xi n and hp : phi.freeVariables = ∅, embedding phi.toEmpty hp back into xi yields phi. The recursive conversion retains the same empty-support guard under both quantifiers. At each binder, lifting the embedding map is the embedding at the successor depth: bound zero and successors agree separately, and there are no Empty free variables. The original subformula is recovered by the induction hypothesis."),
            Paragraph(Text("The data operation univCl returns a Sentence by applying toEmpty to univCl'. A proof of empty support justifies this conversion; the result contains no free-variable payload.")),
            Entry("language-bind", "lMap_bind", "Language maps commute with term assignment",
                Equal(Call("lMap", Id("Phi"), Act(Call("bind", Id("b"), Id("e")), Id("phi"))),
                    Act(Call("bind", Call("compose", Call("termLMap", Id("Phi")), Id("b")), Call("compose", Call("termLMap", Id("Phi")), Id("e"))), Call("lMap", Id("Phi"), Id("phi")))),
                "For arbitrary languages L1 and L2, a language homomorphism Phi, bound assignment b, free assignment e and formula phi, mapping the language after assignment equals assignment by the mapped terms after mapping phi. All source and target variable types and depths remain arbitrary. Under either quantifier, term language mapping commutes with bound shifting and the lifted vector assignments coincide."),
            Paragraph(Text("The following anonymous Lean terms express the general data operations and consequences. All language-map terms use variable {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {Φ : L₁ →ᵥ L₂} in namespace LO.FirstOrder.Semiformula.")),
            Paragraph(Text("free: example (φ : Semiproposition L (n + 1)) : Semiproposition L n := Rewriting.free φ")),
            Paragraph(Text("shift: example (φ : Semiproposition L n) : Semiproposition L n := Rewriting.shift φ")),
            Paragraph(Text("rew_rel_eq_comp: example (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} : ω ▹ rel r v = rel r (ω ∘ v) := rfl")),
            Paragraph(Text("rew_nrel_eq_comp: example (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} : ω ▹ nrel r v = nrel r (ω ∘ v) := rfl")),
            Paragraph(Text("instLawfulSyntacticRewritingSemiproposition: example : LawfulSyntacticRewriting L (Semiproposition L) where")),
            Paragraph(Text("instCoeSemisentenceSemiproposition: example : Coe (Semisentence L n) (Semiproposition L n) := ⟨Rewriting.emb (ξ := ℕ)⟩")),
            Paragraph(Text("rew_eq_of_funEqOn₀: example [DecidableEq ξ₁] {ω₁ ω₂ : Rew L ξ₁ 0 ξ₂ n₂} {φ : Semiformula L ξ₁ 0} (hf : Function.funEqOn (φ.FVar?) (ω₁ ∘ Semiterm.fvar) (ω₂ ∘ Semiterm.fvar)) : ω₁ ▹ φ = ω₂ ▹ φ := rew_eq_of_funEqOn (fun x ↦ Fin.elim0 x) hf")),
            Paragraph(Text("lMap_subst: example (w : Fin k → Semiterm L₁ ξ n) (φ : Semiformula L₁ ξ k) : lMap Φ (φ ⇜ w) = (lMap Φ φ)⇜(Semiterm.lMap Φ ∘ w) := lMap_bind _ _ _")),
            Paragraph(Text("lMap_shift: example (φ : Semiproposition L₁ n) : lMap Φ (@Rew.shift L₁ n ▹ φ) = @Rew.shift L₂ n ▹ lMap Φ φ := lMap_bind _ _ _")),
            Paragraph(Text("lMap_free: example (φ : Semiproposition L₁ (n + 1)) : lMap Φ (@Rew.free L₁ n ▹ φ) = @Rew.free L₂ n ▹ lMap Φ φ := by simp [Rew.free, lMap_bind, Function.comp_def, Matrix.comp_vecConsLast]")),
            Paragraph(Text("lMap_emb: example {ο : Type _} [IsEmpty ο] (φ : Semiformula L₁ ο n) : (lMap Φ (Rewriting.emb φ : Semiformula L₁ ξ n)) = Rewriting.emb (lMap Φ φ) := lMap_bind _ _ _")),
            Paragraph(Text("The source theorem complexity_rew states that every formula rewriting preserves complexity. Its induction argument belongs with the finite-derivation calculus: both quantified clauses of Derivation.eta recurse on phi.free and use phi.complexity as their termination measure. That calculus and this complexity lemma are outside the present collection.")),
            Paragraph(Text("The original mathematical bodies are from FormalizedFormalLogic/Foundation, Foundation/FirstOrder/Basic/Syntax/Rew.lean, revision 30a16ffa93d79d73ab4d02427fa00f50e039bf29. Copyright remains with the Foundation contributors. The Apache-2.0 license and notices are in Library/ConceptDynamics/foundation2026firstorder.md. The action helpers are arranged in one owner and the embedding proof uses a local comparison under each binder. An equivalent interface in the repository's pinned Mathlib replaces this source when a faithful carrier bridge is available.")))));

    private static Formula Act(Formula map, Formula expression) => Call("act", map, expression);

    private static DocumentBlock Entry(string id, string name, string title, Formula formula, string prose) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(F.Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Lemma);
}

/* Complete anonymous statements and derivations.
import D5.S3.ConceptDynamics.ZfcSyntax.FormulaRewriting

namespace LO.FirstOrder.Semiformula

-- RewOne:free
example (φ : Semiproposition L (n + 1)) : Semiproposition L n := Rewriting.free φ

-- RewOne:shift
example (φ : Semiproposition L n) : Semiproposition L n := Rewriting.shift φ

-- RewOne:rew_rel_eq_comp
example (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} :
    ω ▹ rel r v = rel r (ω ∘ v) := rfl

-- RewOne:rew_nrel_eq_comp
example (ω : Rew L ξ₁ n₁ ξ₂ n₂) {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} :
    ω ▹ nrel r v = nrel r (ω ∘ v) := rfl

-- RewOne:instLawfulSyntacticRewritingSemiproposition
example : LawfulSyntacticRewriting L (Semiproposition L) where

-- RewOne:instCoeSemisentenceSemiproposition
example : Coe (Semisentence L n) (Semiproposition L n) := ⟨Rewriting.emb (ξ := ℕ)⟩

-- RewTwo:rew_eq_of_funEqOn₀
example [DecidableEq ξ₁] {ω₁ ω₂ : Rew L ξ₁ 0 ξ₂ n₂} {φ : Semiformula L ξ₁ 0}
    (hf : Function.funEqOn (φ.FVar?) (ω₁ ∘ Semiterm.fvar) (ω₂ ∘ Semiterm.fvar)) : ω₁ ▹ φ = ω₂ ▹ φ :=
  rew_eq_of_funEqOn (fun x ↦ Fin.elim0 x) hf

section
variable {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {Φ : L₁ →ᵥ L₂}

-- RewTwo:lMap_subst
example (w : Fin k → Semiterm L₁ ξ n) (φ : Semiformula L₁ ξ k) :
    lMap Φ (φ ⇜ w) = (lMap Φ φ)⇜(Semiterm.lMap Φ ∘ w) := lMap_bind _ _ _

-- RewTwo:lMap_shift
example (φ : Semiproposition L₁ n) : lMap Φ (@Rew.shift L₁ n ▹ φ) = @Rew.shift L₂ n ▹ lMap Φ φ := lMap_bind _ _ _

-- RewTwo:lMap_free
example (φ : Semiproposition L₁ (n + 1)) : lMap Φ (@Rew.free L₁ n ▹ φ) = @Rew.free L₂ n ▹ lMap Φ φ := by
  simp [Rew.free, lMap_bind, Function.comp_def, Matrix.comp_vecConsLast]

-- RewTwo:lMap_emb
example {ο : Type _} [IsEmpty ο] (φ : Semiformula L₁ ο n) :
    (lMap Φ (Rewriting.emb φ : Semiformula L₁ ξ n)) = Rewriting.emb (lMap Φ φ) := lMap_bind _ _ _

end
end LO.FirstOrder.Semiformula
*/
