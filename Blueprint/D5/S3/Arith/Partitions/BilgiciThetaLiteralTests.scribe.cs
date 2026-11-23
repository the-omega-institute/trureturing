using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Partitions;

internal sealed class BilgiciThetaLiteralTestsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Partitions/BilgiciThetaLiteralTests.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/bilgici2026ninecolored");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The tests of the full weight component.",
        H("The tests of the full weight component"),
        Blocks(
            Describe.Lean(DescribeId.Create("bilgici-literalf11-eigengrade"),
                DeclarationHandle.Create(Prefix + "literalF11_eigengrade"), H("The grade and character of the literal component"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The weight-eleven component of the entire product B times C cubed lies in the "
                    + "character-four quotient subspace of degree seven and weight eleven. Signed full-field "
                    + "reindexing gives its character."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bilgici-literalf11-epsilon-zero"),
                DeclarationHandle.Create(Prefix + "literalF11_epsilon_zero"), H("Vanishing of the dual-number test"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The centered filter is one minus the centered quadratic form to the eighteenth power. "
                    + "After dual-number evaluation the epsilon coefficient is a full-field moment of a "
                    + "polynomial of degree at most 54. Each monomial has some coordinate exponent below 18, "
                    + "so its moment vanishes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bilgici-literalf11-trace-thirty"),
                DeclarationHandle.Create(Prefix + "literalF11_trace_thirty"), H("The leading trace coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The lowest trace order is 30, contributed by B at the positive pair (3, 9) and C at "
                    + "index 9 in all three factors. The degree-thirty coefficient is one and survives in the "
                    + "theta quotient."))), DescribeRole.Theorem))));
}
