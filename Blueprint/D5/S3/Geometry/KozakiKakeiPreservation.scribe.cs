using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiPreservationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiPreservation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rotation or reflection preserves or exchanges the matching products, with a common orientation factor in the signed equation.",
        H("Dihedral permutations preserve the written level"),
        Blocks(
            Theorem("dihedral_preservesLevel", "Dihedral inclusion",
                "Cyclic transport preserves or exchanges the two parity classes of edges. Accounting for the reversed closing edge and the orientation of a reflection transfers equality of the products.",
                DihedralPreservesLevel()))));

    private static DocumentBlock Theorem(string name, string title, string prose, Formula statement) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Theorem);

    private static Formula DihedralPreservesLevel() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("s"),
        Sp, Colon, Sp, Word("Perm"), Open, Word("Col"), Open, F.Id("m"), Close, Close, Comma, Sp, D(2), Sp, Le,
        Sp, F.Id("m"), Sp, Implies, Sp, Word("Dihedral"), Open, F.Id("s"), Close, Sp, Implies, Sp,
        Word("PreservesLevel"), Open, F.Id("s"), Close);

    private static Formula Word(string value) => Seq(Operatorname, Grp(F.Id(value)));

    private static string NodeId(string name) =>
        "frieze-preservation-" + name.ToLowerInvariant().Replace('_', '-');
}
