using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiPreservationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiPreservation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rotation or reflection preserves or exchanges the matching products, with a common orientation factor in the signed equation.",
        H("Dihedral permutations preserve the written level"),
        Blocks(
            Theorem("minor_swap", "Reversing an ordered minor",
                "Exchanging the two arguments of a minor multiplies it by minus one."),
            Theorem("dihedral_preservesLevel", "Dihedral inclusion",
                "Cyclic transport preserves or exchanges the two parity classes of edges. Accounting for the reversed closing edge and the orientation of a reflection transfers equality of the products."))));

    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static string NodeId(string name) =>
        "frieze-preservation-" + name.ToLowerInvariant().Replace('_', '-');
}
