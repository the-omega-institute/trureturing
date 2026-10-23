using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class PresburgerDecisionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recursive Cooper elimination computes the truth of every integer formula.", H("Integer decisions by recursive elimination"),
        Blocks(Paragraph(Text("Formula.quantifierEliminate leaves QF formulas alone, maps Boolean constructors recursively and applies Cooper.eliminate to the recursively converted body of an existential. Derived universal quantifiers are not-exists-not, so arbitrary alternation and nested negation are included.")),
            Paragraph(Text("decideHolds evaluates the resulting QF under the supplied integer list. holdsDecidable branches on this Bool and transfers its equality-to-true proof to Formula.holds. decideSentence evaluates at the empty valuation; presburgerArithmetic_decidable uses the same executable decision. These definitions and proofs are upstream ProveIt results, separate from the native Nat compiler. No recursion-theoretic Computable theorem or complexity bound is asserted.")),
            Describe.Lean(DescribeId.Create("holds-iff-quantifiereliminate"),
            DeclarationHandle.Create("D5/S0/Computability/PresburgerDecision.holds_iff_quantifierEliminate"),
            H("Full formula semantics"), StatementSource.FromAuthor(F.Disp(A("p", V("Formula"), A("xs", Call("List", V("Int")), I(Call("holds",V("p"),V("xs")), E(Call("eval",Call("quantifierEliminate",V("p")),V("xs")),V("true"))))))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("Formula induction proves the Boolean cases directly. The existential case combines the induction hypothesis at x::xs with Cooper.eliminate_correct."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("decideholds-eq-true-iff"),
            DeclarationHandle.Create("D5/S0/Computability/PresburgerDecision.decideHolds_eq_true_iff"),
            H("Executable Bool contract"), StatementSource.FromAuthor(F.Disp(A("p", V("Formula"), A("xs", Call("List", V("Int")), I(E(Call("decideHolds",V("p"),V("xs")),V("true")),Call("holds",V("p"),V("xs"))))))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("The decision is definitionally the eliminated formula evaluation; the previous equivalence is reversed. This contract is the integer decision interface used by NatPresburger.test."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("decidesentence-eq-true-iff"),
            DeclarationHandle.Create("D5/S0/Computability/PresburgerDecision.decideSentence_eq_true_iff"),
            H("Empty valuation convention"), StatementSource.FromAuthor(F.Disp(A("p", V("Sentence"), I(E(Call("decideSentence",V("p")),V("true")),Call("holds",V("p"),V("nil")))))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("This is the same decision contract specialized to the empty integer valuation. It does not require a new elimination proof."))), DescribeRole.Theorem)), [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/PresburgerElimination"))]));

    private static Formula V(string name) => F.Id(name);
    private static Formula A(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula E(Formula left, Formula right) => F.Seq(left, F.Sp, F.Eq, F.Sp, right);
    private static Formula I(Formula left, Formula right) => F.Seq(F.Open, left, F.Close, F.Sp, F.Iff, F.Sp, F.Open, right, F.Close);
}
