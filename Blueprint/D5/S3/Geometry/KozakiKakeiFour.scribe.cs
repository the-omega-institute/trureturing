using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiFour.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At four columns the two signed evaluations of a pair indicator separate edges and diagonals directly.",
        H("The signed four-column branch"),
        Blocks(
            Theorem("dihedral_of_scalar_four", "Four-column necessity",
                "The signed quadratic evaluates to one on the indicator of an edge and minus two on the indicator of a diagonal. Among the images of the two edges incident with a fixed vertex, at least one is an edge. The scalar must be one, so every edge maps to an edge.",
                DihedralOfScalarFour()),
            Theorem("dihedral_of_preservesLevel", "Necessity on the whole size range",
                "Apply scalar rigidity to the admissible constant matrices. Then use signed pair evaluations for m equal to two and recovery by support counts for every m at least four.",
                DihedralOfPreservesLevel()))));

    private static DocumentBlock Theorem(string name, string title, string prose, Formula statement) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Theorem);

    private static Formula DihedralOfScalarFour() => Seq(
        Forall, Sp, F.Id("s"), Sp, Colon, Sp, Word("Perm"), Open, Word("Col"), Open, D(2), Close, Close, Comma,
        Sp, Forall, Sp, F.Id("c"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))), Comma, Sp, Word("rename"), Open,
        F.Id("s"), Comma, F.Id("F"), Open, D(2), Close, Close, Sp, Eq, Sp, F.Id("C"), Open, F.Id("c"), Close,
        Sp, Cdot, Sp, F.Id("F"), Open, D(2), Close, Sp, Implies, Sp, Word("Dihedral"), Open, F.Id("s"), Close);

    private static Formula DihedralOfPreservesLevel() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Forall, Sp, F.Id("s"),
        Sp, Colon, Sp, Word("Perm"), Open, Word("Col"), Open, F.Id("m"), Close, Close, Comma, Sp, D(2), Sp, Le,
        Sp, F.Id("m"), Sp, Implies, Sp, F.Id("m"), Sp, Neq, Sp, D(3), Sp, Implies, Sp, Word("PreservesLevel"),
        Open, F.Id("s"), Close, Sp, Implies, Sp, Word("Dihedral"), Open, F.Id("s"), Close);

    private static Formula Word(string value) => Seq(Operatorname, Grp(F.Id(value)));

    private static string NodeId(string name) =>
        "frieze-four-" + name.ToLowerInvariant().Replace('_', '-');
}
