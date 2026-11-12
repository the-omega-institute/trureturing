using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves;
internal sealed class RootTwoResidualStripDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/RootTwoResidualStrip." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The current compiler statement below supplies the exact telescope, hypotheses and conclusion. The full domain and original boundaries in this document apply."))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full root-two residual strip candidate bound", H("Full root-two residual strip candidate bound"),
        Blocks(
            Paragraph(Text("For every integer a>=5 the full a<=b<=2a-3 residual strip has at most4(a-2) ordered candidate pairs. Actual ideal-intersection graph integrality on four distinct primes implies membership. The graph hypotheses, both root2/root3 fibers and all positive c>=a are retained. This is not a criterion for integrality, uniform bound in a or emptiness proof.")),
            Paragraph(Text("Source: original Nikandish problem; Ma/Nikandish/Zhang supplied manuscripts at PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02. Exact source blob and attribution are retained in Lean. All O1-O9, L1-L21/F1-F17, C1-C16 outcomes and original rights/publication boundaries remain binding. Exact n7 and its pause, generalQ3, a6 certification and finite-enumeration reproduction limits are unchanged. Unfinished faithful escape registration is disclosed in issue#28398; disclosure is not audit completion.")),
            Item("cardinal-bound", "cardinal_bound", "cardinal bound"),
            Item("actual-integral-mem", "actual_integral_mem", "actual integral mem")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/RootTwoTailCurve"))]));
}
