using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class SixSupportEndpointTwoMaximumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Received complete three-prime statements; actual objects and original domains retained.",
        H("SixSupportEndpointTwoMaximum"),
        Blocks(
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointTwoMaximum.result"), H("result"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every ordered real triple 4<=a<=b<=c with c>=3a-4, the exact full six-cell characteristic quotient has h_C(2)>0. The complete 88-coefficient source identity and derived inverse rational parameters cover the entire interval a<=b<2a-2; the remaining middle range uses the sharp-alpha theorem. Every endpoint and parameter boundary is retained."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportIdealIntersectionLift"))]));
}
