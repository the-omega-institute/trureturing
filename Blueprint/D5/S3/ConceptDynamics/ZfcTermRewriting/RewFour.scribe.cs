using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ZfcTermRewriting;

internal sealed class RewFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/foundation2026firstorder");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seven lawful capture-avoiding rewriting and substitution identities over arbitrary signatures.",
        H("RewFour"),
        Blocks(
            Paragraph(Text("Throughout, L is an arbitrary first-order signature and S is a family indexed by natural numbers, with LCWQ S, SyntacticRewriting L S S and LawfulSyntacticRewriting L S. The map f sends natural-number free variables to syntactic terms over L. In the formulas, act is the rewriting action, lift sends x to bShift(f(x)), extend sends zero to the free variable zero and successor x to shift(f(x)), and insert sends zero to t and successor x to the free variable x. The operation cast substitutes the empty vector into an element of S(0); single denotes substitution of one term.")),
            Entry("free-rewrite", "free_rewrite_eq", "Freeing commutes with lifted rewriting",
                Equal(Call("free", Act(Call("lift", Id("f")), Id("phi"))),
                    Act(Call("extend", Id("f")), Call("free", Id("phi")))),
                "For every phi in S(1), freeing after rewriting with the bound-variable lift agrees with rewriting the freed expression by extend(f)."),
            Entry("shift-rewrite", "shift_rewrite_eq", "Shifting commutes with rewriting",
                Equal(Call("shift", Act(Id("f"), Id("phi"))),
                    Act(Call("extend", Id("f")), Call("shift", Id("phi")))),
                "For every phi in S(0), shifting after rewriting agrees with rewriting the shifted expression by extend(f)."),
            Entry("rewrite-subst", "rewrite_subst_eq", "Rewriting commutes with single substitution",
                Equal(Act(Id("f"), Call("single", Id("phi"), Id("t"))),
                    Call("single", Act(Call("lift", Id("f")), Id("phi")), Call("rewriteTerm", Id("f"), Id("t")))),
                "For every syntactic term t and phi in S(1), rewriting a substitution agrees with lifted rewriting followed by substitution of the rewritten term."),
            Entry("free-subst-nil", "free_subst_nil", "Freeing an empty substitution shifts",
                Equal(Call("free", Call("cast", Id("phi"))), Call("shift", Id("phi"))),
                "For every phi in S(0), freeing its empty-vector substitution equals its shift."),
            Entry("rewrite-subst-nil", "rewrite_subst_nil", "Lifted rewriting preserves the empty substitution",
                Equal(Act(Call("lift", Id("f")), Call("cast", Id("phi"))),
                    Call("cast", Act(Id("f"), Id("phi")))),
                "For every phi in S(0), lifted rewriting of the empty-vector substitution equals the empty-vector substitution after rewriting."),
            Entry("cast-subst", "cast_subst_eq", "Single substitution cancels an empty-vector cast",
                Equal(Call("single", Call("cast", Id("phi")), Id("t")), Id("phi")),
                "For every syntactic term t and phi in S(0), substituting t after the empty-vector cast returns phi."),
            Entry("rewrite-free-subst", "rewrite_free_eq_subst", "Rewriting a freed expression realizes substitution",
                Equal(Act(Call("insert", Id("t")), Call("free", Id("phi"))),
                    Call("single", Id("phi"), Id("t"))),
                "For every syntactic term t and phi in S(1), rewriting free(phi) by insert(t) equals single substitution of t into phi."),
            Paragraph(Text("These are retained prerequisite APIs for first-order finite derivations. They do not establish the complete CSA defining graphs, definition elimination, ZFC conservativity or model existence.")),
            Paragraph(Text("The seven mathematical commands are retained from Foundation/Syntax/Predicate/Rew.lean, lines 955-989 within capacity span 954-1080, at revision 30a16ffa93d79d73ab4d02427fa00f50e039bf29. Attribution, modification notices, the complete Apache-2.0 license and the replacement condition are in Library/ConceptDynamics/foundation2026firstorder.md. Compiler companions are not independently authored theorems.")))));

    private static Formula Act(Formula map, Formula expression) =>
        Call("act", Call("rewrite", map), expression);

    private static DocumentBlock Entry(string id, string name, string title, Formula formula, string prose) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(F.Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Lemma);
}
