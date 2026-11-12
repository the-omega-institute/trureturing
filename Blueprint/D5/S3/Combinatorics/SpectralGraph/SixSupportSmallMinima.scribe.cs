using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class SixSupportSmallMinimaDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Received complete three-prime statements; actual objects and original domains retained.",
        H("SixSupportSmallMinima"),
        Blocks(
            Describe.Lean(DescribeId.Create("unit-identity"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportSmallMinima.unit_identity"), H("unit_identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("On the full real unit-exponent plane, h(1)=b²c²(b+c-3)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unit-interval"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportSmallMinima.unit_interval"), H("unit_interval"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Every positive real b,c with b+c greater than three gives a quotient root in (0,1)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unit-actual"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportSmallMinima.unit_actual"), H("unit_actual"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Every positive integer unit-exponent triple with the indicated sum condition is consumed by the actual ideal graph; repeated exceptional sums are covered by the repeated theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("minimum-two-first"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportSmallMinima.minimum_two_first"), H("minimum_two_first"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The complete shifted first positive identity at a=2,b=3,c at least five."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("minimum-two-second"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportSmallMinima.minimum_two_second"), H("minimum_two_second"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The complete two-variable positive identity at a=2,b at least four,c at least b+1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("minimum-two-actual"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportSmallMinima.minimum_two_actual"), H("minimum_two_actual"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Every fully distinct sorted positive integer triple with minimum two has nonintegral actual spectrum, including the separate (2,3,4) root in (1,3/2)."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportIdealIntersectionLift"))]));
}
