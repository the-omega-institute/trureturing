using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraCoreFrozenWalkDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/gupta2026miuradegrees");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite signed contraction on the actual rectangular height grid.", H("Uniform side difference"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuracorefrozenwalk-0"),
                DeclarationHandle.Create(Prefix + "alignedExt"), H("Aligned walk extrema"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("An aligned row records two equal side signs and the corresponding existing vertical signs of a strict extremum."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracorefrozenwalk-1"),
                DeclarationHandle.Create(Prefix + "cascade_down"), H("Downward propagation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A row with aligned side signs and a vertical step preventing an extremum propagates to the bottom endpoint, where extremum-freeness gives a contradiction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorefrozenwalk-2"),
                DeclarationHandle.Create(Prefix + "cascade_up"), H("Upward propagation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The analogous propagation toward the top endpoint also contradicts extremum-freeness."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorefrozenwalk-3"),
                DeclarationHandle.Create(Prefix + "extremumFree_rainbow"), H("Opposite side signs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For three compatible unit-step walks with no aligned extremum, the two horizontal side differences sum to zero at every row."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorefrozenwalk-4"),
                DeclarationHandle.Create(Prefix + "rainbow_dL_const"), H("Uniform side difference"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("If the two side differences sum to zero at every row and all three walks have unit increments, each adjacent pair of rows has the same left difference."))), DescribeRole.Theorem))));
}
