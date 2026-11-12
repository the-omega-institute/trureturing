using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class SixSupportUniformTailDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact received three-prime spectral statements with actual ideal-graph consumers.",
        H("SixSupportUniformTail"),
        Blocks(
            Describe.Lean(DescribeId.Create("zero-negative"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportUniformTail.zero_negative"), H("zero_negative"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The actual characteristic quotient is strictly negative at zero for every positive real triple."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("one-positive"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportUniformTail.one_positive"), H("one_positive"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For all ordered real 2<=a<=b<=c with c>=4a^2-2a, h_C(1) is strictly positive. The original coefficient comparison and positive K(a) expansion are exact kernel identities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportUniformTail.result"), H("result"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The complete real uniform tail has a quotient root in (0,1), with no upper bound on either remaining exponent."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-nonintegral"), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportUniformTail.actual_nonintegral"), H("actual_nonintegral"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Every positive integer triple in that full tail, for every three distinct primes, has a nonintegral actual ideal-intersection Laplacian. The genuine ideal-graph correspondence consumes the root."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/SixSupportIdealIntersectionLift"))]));
}
