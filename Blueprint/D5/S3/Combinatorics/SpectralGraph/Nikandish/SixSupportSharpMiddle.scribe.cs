using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class SixSupportSharpMiddleDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Received complete three-prime statements; actual objects and original domains retained.",
        H("SixSupportSharpMiddle"),
        Blocks(
            Describe.Lean(DescribeId.Create("alpha"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportSharpMiddle.alpha"), H("alpha"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The exact sharp real threshold (7+sqrt(13))/3."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("alpha-gt-three"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportSharpMiddle.alpha_gt_three"), H("alpha_gt_three"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The threshold strictly exceeds three, without numerical approximation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportSharpMiddle.result"), H("result"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every real a at least alpha, b at least 2a-2 and c at least b, h(2) is nonnegative; it is zero exactly when a=alpha and b=c=2a-2. The unique equality boundary is retained."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("zero-middle-bound"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportSharpMiddle.zero_middle_bound"), H("zero_middle_bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Every endpoint-two zero above the sharp threshold has b strictly below 2a-2; this does not assert that the entire integer endpoint surface is empty."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportIdealIntersectionLift"))]));
}
