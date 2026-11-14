using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves;
internal sealed class A6QuadraticIntegersDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6QuadraticIntegers." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The current compiler statement below supplies the exact telescope, hypotheses and conclusion. The full domain and original boundaries in this document apply."))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full quadratic integer ring", H("Full quadratic integer ring"),
        Blocks(
            Paragraph(Text("Every element of the actual integral closure in Q(sqrt43645) is exactly m+n(1+sqrt43645)/2, with arbitrary integer m,n. The trace/norm and denominator-squarefree arguments retain every half-integer fiber. This equality identifies the entire ring, not only a chosen order.")),
            Paragraph(Text("Source: original Nikandish problem; Ma/Nikandish/Zhang supplied manuscripts at PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02. Exact source blob and attribution are retained in Lean. All O1-O9, L1-L21/F1-F17, C1-C16 outcomes and original rights/publication boundaries remain binding. Exact n7 and its pause, generalQ3, a6 certification and finite-enumeration reproduction limits are unchanged.")),
            Item("theta-integral", "theta_integral", "theta integral"),
            Item("integral-iff-integer-coordinates", "integral_iff_integer_coordinates", "integral iff integer coordinates"),
            Item("full-ring-eq-adjoin", "full_ring_eq_adjoin", "full ring eq adjoin")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6EllipticModels"))]));
}
