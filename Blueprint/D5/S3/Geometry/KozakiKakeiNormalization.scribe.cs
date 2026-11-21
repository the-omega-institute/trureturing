using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiNormalization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The written level equation is precisely the condition for an admissible matrix to have a unique representative in ordered normal form.",
        H("Existence and uniqueness of the ordered normal form"),
        Blocks(
            Definition("UnitAdjacent", "Unit consecutive minors",
                "Each successive pair in linear column order has minor one."),
            Theorem("normalized_level", "A normalized matrix is on the level",
                "All factors of both written matching products are one."),
            Theorem("normalized_exists", "Existence of the ordered representative",
                "An invertible row operation fixes the first two columns. The initial diagonal factors fix the third, and a recurrence sets the remaining consecutive minors to one. The level equation then forces the closing minor to be one."),
            Theorem("normalized_unique_of_equiv", "Uniqueness within a matrix class",
                "The first two fixed columns force the left transformation to be diagonal. The third forces its entries to agree, and the consecutive minors determine all remaining column factors."),
            Theorem("normalized_representative_iff", "Characterization of normalizable matrices",
                "For every admissible matrix, the existence of exactly one normalized equivalent matrix is equivalent to the literal equality of the two determinant products."))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static string NodeId(string name) =>
        "frieze-normalization-" + name.ToLowerInvariant().Replace('_', '-');
}
