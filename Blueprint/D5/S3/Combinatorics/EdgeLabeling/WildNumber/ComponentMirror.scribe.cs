using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling.WildNumber;

internal sealed class ComponentMirrorDocument : IScribeDocumentDefinition
{

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite edge-colored graphs and their greedy color-connecting sets.", H("ComponentMirror"), Blocks(
            Describe.Lean(DescribeId.Create("wild-number-componentmirror-renamelabels"),
                DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/WildNumber/ComponentMirror.renameLabels"), H("renameLabels"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(Word("V"), Sp, Colon, Sp, Word("Type"))), Sp, OpenBracket, Sp, Word("DecidableEq"), Sp, Word("V"), Sp, CloseBracket, Sp, Parenthesized(Seq(Rho, Sp, Colon, Sp, Word("V"), Sp, To, Sp, Word("V"))), Sp, Parenthesized(Seq(Word("u"), Sp, Word("v"), Sp, Word("x"), Sp, Colon, Sp, Word("V"))), Sp, Comma, Sp, Word("renameLabels"), Sp, Rho, Sp, Word("u"), Sp, Word("v"), Sp, Word("x"), Sp, Eq, Sp, Word("Finset"), Sp, Dot, Sp, Word("piecewise"), Sp, Parenthesized(Seq(OpenBrace, Sp, Rho, Sp, Word("u"), Sp, CloseBrace, Sp, Colon, Sp, Word("Finset"), Sp, Word("V"))), Sp, Parenthesized(Seq(Word("Function"), Sp, Dot, Sp, Word("const"), Sp, Word("V"), Sp, Parenthesized(Seq(Rho, Sp, Word("v"))))), Sp, Word("id"), Sp, Parenthesized(Seq(Rho, Sp, Word("x")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Starting with one label per vertex, processing an edge replaces every copy of one endpoint label by the other endpoint label. The distinct final labels count the connected components."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("wild-number-componentmirror-labels"),
                DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/WildNumber/ComponentMirror.labels"), H("labels"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(Word("V"), Sp, Colon, Sp, Word("Type"))), Sp, OpenBracket, Sp, Word("DecidableEq"), Sp, Word("V"), Sp, CloseBracket, Sp, Comma, Sp, Parenthesized(Seq(Word("labels"), Sp, Parenthesized(Seq(OpenBracket, Sp, CloseBracket, Sp, Colon, Sp, Word("List"), Sp, Parenthesized(Seq(Word("V"), Sp, Times, Sp, Word("V"))))), Sp, Eq, Sp, Word("id"))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(Word("u"), Sp, Word("v"), Sp, Colon, Sp, Word("V"))), Sp, Parenthesized(Seq(Word("L"), Sp, Colon, Sp, Word("List"), Sp, Parenthesized(Seq(Word("V"), Sp, Times, Sp, Word("V"))))), Sp, Comma, Sp, Word("labels"), Sp, Parenthesized(Seq(Word("List"), Sp, Dot, Sp, Word("cons"), Sp, Parenthesized(Seq(Word("u"), Sp, Comma, Sp, Word("v"))), Sp, Word("L"))), Sp, Eq, Sp, Word("renameLabels"), Sp, Parenthesized(Seq(Word("labels"), Sp, Word("L"))), Sp, Word("u"), Sp, Word("v")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Starting with one label per vertex, processing an edge replaces every copy of one endpoint label by the other endpoint label. The distinct final labels count the connected components."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("wild-number-componentmirror-componentcount"),
                DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/WildNumber/ComponentMirror.componentCount"), H("componentCount"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(Word("V"), Sp, Colon, Sp, Word("Type"))), Sp, OpenBracket, Sp, Word("Fintype"), Sp, Word("V"), Sp, CloseBracket, Sp, OpenBracket, Sp, Word("DecidableEq"), Sp, Word("V"), Sp, CloseBracket, Sp, Parenthesized(Seq(Word("L"), Sp, Colon, Sp, Word("List"), Sp, Parenthesized(Seq(Word("V"), Sp, Times, Sp, Word("V"))))), Sp, Comma, Sp, Word("componentCount"), Sp, Word("L"), Sp, Eq, Sp, Parenthesized(Seq(Word("Finset"), Sp, Dot, Sp, Word("univ"), Sp, Dot, Sp, Word("image"), Sp, Parenthesized(Seq(Word("labels"), Sp, Word("L"))))), Sp, Dot, Sp, Word("card")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Starting with one label per vertex, processing an edge replaces every copy of one endpoint label by the other endpoint label. The distinct final labels count the connected components."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("wild-number-componentmirror-componentcount-eq-kappa"),
                DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/WildNumber/ComponentMirror.componentCount_eq_kappa"), H("componentCount eq kappa"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, OpenBrace, Sp, Word("V"), Sp, Colon, Sp, Word("Type"), Sp, CloseBrace, Sp, OpenBracket, Sp, Word("Fintype"), Sp, Word("V"), Sp, CloseBracket, Sp, OpenBracket, Sp, Word("DecidableEq"), Sp, Word("V"), Sp, CloseBracket, Sp, Parenthesized(Seq(Word("L"), Sp, Colon, Sp, Word("List"), Sp, Parenthesized(Seq(Word("V"), Sp, Times, Sp, Word("V"))))), Sp, Comma, Sp, Word("ComponentMirror"), Sp, Dot, Sp, Word("componentCount"), Sp, Word("L"), Sp, Eq, Sp, Word("Nat"), Sp, Dot, Sp, Word("card"), Sp, Parenthesized(Seq(Word("SimpleGraph"), Sp, Dot, Sp, Word("fromRel"), Sp, Word("fun"), Sp, Word("u"), Sp, Word("v"), Sp, Mapsto, Sp, Parenthesized(Seq(Word("u"), Sp, Comma, Sp, Word("v"))), Sp, InMacro, Sp, Word("L"))), Sp, Dot, Sp, Word("ConnectedComponent")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Starting with one label per vertex, processing an edge replaces every copy of one endpoint label by the other endpoint label. The distinct final labels count the connected components."))), DescribeRole.Theorem))));

    private static Formula Word(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
}
