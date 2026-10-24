using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ComponentPacking;

internal sealed class AhanjidehEkimYildizZUpperDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZUpper.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/ahanjidehekimyildiz2022matching");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite graph structure, degree counting, and perfect matchings.",
        H("AhanjidehEkimYildizZUpper"),
        Blocks(
            Node("aey-upper-theorem-attainment", "attainment", Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("large"), Colon, Sp, Seq(Operatorname, Grp(F.Id("Bool"))))), Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Seq(Parenthesized(Parenthesized(Seq(D(5), Sp, Leq, Sp, F.Id("k")))), To, Parenthesized(Parenthesized(Seq(Seq(F.Id("let"), Sp, F.Id("d"), Sp, Eq, Sp, D(4), Sp, Cdot, Sp, F.Id("k"), Sp, Plus, Sp, Parenthesized(Seq(F.Id("if"), Sp, F.Id("large"), Sp, F.Id("then"), Sp, D(3), Sp, F.Id("else"), Sp, D(1)))), Semi, Sp, Seq(Exists, Sp, Parenthesized(Seq(F.Id("N"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Seq(Exists, Sp, Parenthesized(Seq(F.Id("G"), Colon, Sp, Seq(Seq(Operatorname, Grp(F.Id("SimpleGraph"))), Sp, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("Fin"))), Sp, F.Id("N")))))), Comma, Sp, Seq(Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("IsAlmostRegular"))), Sp, F.Id("G"), Sp, F.Id("d"))), Land, Parenthesized(Seq(Parenthesized(Seq(F.Id("G"), Sp, Dot, Sp, Seq(Operatorname, Grp(F.Id("CliqueFree"))), Sp, D(3))), Land, Parenthesized(Seq(Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("IsFactorCritical"))), Sp, F.Id("G"))), Land, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("matchingNumber"))), Sp, F.Id("G"), Sp, Eq, Sp, Seq(Operatorname, Grp(F.Id("Nat"))), Sp, Dot, Sp, Seq(Operatorname, Grp(F.Id("div"))), Sp, Parenthesized(Seq(D(5), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))))), Sp, D(4))))))))))))))))),
                "Proposition 4.3, page 8, gives the upper-bound graphs. The two thirteen-bag constructions give almost regular, triangle-free, factor-critical graphs for degrees 4k + 1 and 4k + 3. Their orders are twice the stated matching number plus one. Natural division denotes floor division.", "attainment", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source))),
        []));
    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
