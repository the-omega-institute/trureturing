using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Nikandish;
internal sealed class BalancedPairDeterminantDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairDeterminant." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete balanced-region spectral determinant positivity.", H("Complete balanced-region spectral determinant positivity."),
        Blocks(
            Paragraph(Text("Source: four-prime-single-pair-balanced, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The original parameter domains, attribution and failed-method limitations are retained. General four-prime and higher-prime Q3 remain open outside the stated families. Original academic approval and publication boundaries are unchanged.")),
            Item("shift", "shifted_positive", "Every real spectral value at or below three is excluded", "Over the complete domain a<=b<=c<=2a-6, the determinant at every x<=3 is strictly positive. The nonnegative variables b-a, c-b and 2a-c-6 retain all boundaries. All symbolic coefficients are checked by Lean ring reduction."),
            Item("lower", "eigenvalue_gt_three", "Every actual weighted-tensor eigenpair is above three", "The determinant identity applies to every nonzero real tensor eigenvector; it is not a finite set of sample eigenvalues.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionDeterminants"))]));
}
