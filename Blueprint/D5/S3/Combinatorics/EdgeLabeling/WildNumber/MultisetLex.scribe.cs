using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling.WildNumber;

internal sealed class MultisetLexDocument : IScribeDocumentDefinition
{

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite edge-colored graphs and their greedy color-connecting sets.", H("MultisetLex"), Blocks(
            Describe.Lean(DescribeId.Create("wild-number-multisetlex-sort-add-lex-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/WildNumber/MultisetLex.sort_add_lex_iff"), H("sort add lex iff"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(Word("s"), Sp, Word("t"), Sp, Word("u"), Sp, Colon, Sp, Word("Multiset"), Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Word("List"), Sp, Dot, Sp, Word("Lex"), Sp, Parenthesized(Seq(Word("fun"), Sp, Word("x1"), Sp, Word("x2"), Sp, Mapsto, Sp, Word("x1"), Sp, Lt, Sp, Word("x2"))), Sp, Parenthesized(Seq(Parenthesized(Seq(Word("s"), Sp, Plus, Sp, Word("u"))), Sp, Dot, Sp, Word("sort"), Sp, Word("fun"), Sp, Word("x1"), Sp, Word("x2"), Sp, Mapsto, Sp, Word("x1"), Sp, Geq, Sp, Word("x2"))), Sp, Parenthesized(Seq(Parenthesized(Seq(Word("t"), Sp, Plus, Sp, Word("u"))), Sp, Dot, Sp, Word("sort"), Sp, Word("fun"), Sp, Word("x1"), Sp, Word("x2"), Sp, Mapsto, Sp, Word("x1"), Sp, Geq, Sp, Word("x2"))), Sp, Iff, Sp, Word("List"), Sp, Dot, Sp, Word("Lex"), Sp, Parenthesized(Seq(Word("fun"), Sp, Word("x1"), Sp, Word("x2"), Sp, Mapsto, Sp, Word("x1"), Sp, Lt, Sp, Word("x2"))), Sp, Parenthesized(Seq(Word("s"), Sp, Dot, Sp, Word("sort"), Sp, Word("fun"), Sp, Word("x1"), Sp, Word("x2"), Sp, Mapsto, Sp, Word("x1"), Sp, Geq, Sp, Word("x2"))), Sp, Parenthesized(Seq(Word("t"), Sp, Dot, Sp, Word("sort"), Sp, Word("fun"), Sp, Word("x1"), Sp, Word("x2"), Sp, Mapsto, Sp, Word("x1"), Sp, Geq, Sp, Word("x2")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Sorting natural-number multisets in nonincreasing order gives a lexicographic comparison that is preserved and reflected by addition of a common multiset."))), DescribeRole.Theorem))));

    private static Formula Word(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
}
