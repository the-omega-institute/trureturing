using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SemiMeanderSecondDiagonal;

internal sealed class Stage5Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage5.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/hogan2026a400429");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The connected source matchings reduce to canonical prefix pairs, whose finite fibers give the polynomial count.",
        H("Canonical Prefix Count"),
        Blocks(
            Describe.Lean(DescribeId.Create("canonical-card"),
                DeclarationHandle.Create(Prefix + "canonical_card"),
                H("Count canonical pairs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The canonical prefix pairs split into finite families whose cardinalities can be counted directly."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("arithmetic"),
                DeclarationHandle.Create(Prefix + "canonical_count_arithmetic"),
                H("Polynomial arithmetic"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The canonical family count simplifies to the second-diagonal polynomial after substituting n minus four."))),
                DescribeRole.Theorem)),
        []));
}
